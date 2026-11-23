import Gaussian

namespace Skolem.Research

/-- Shape of an odd power of r+is. The real part is r*A, where A is
(2j+1)(-s²)^j modulo r². -/
private theorem odd_power_shape (r s : Int) (j : Nat) :
    ∃ A B N c d : Int, gpow (r,s) (2*j+1) = (r*A, s*B) ∧
      A = (2*(j:Int)+1)*N + r*r*c ∧ B = N + r*r*d := by
  induction j with
  | zero => exact ⟨1,1,1,0,0, by simp [gpow,gmul], by simp, by simp⟩
  | succ j ih =>
    obtain ⟨A,B,N,c,d,h,hA,hB⟩ := ih
    refine ⟨A*(r*r-s*s) - 2*s*s*B, 2*r*r*A + B*(r*r-s*s), -(s*s)*N,
      (2*(j:Int)+1)*N + c*(r*r-s*s) - 2*s*s*d, 2*A + N + d*(r*r-s*s), ?_, ?_, ?_⟩
    · rw [show 2*(j+1)+1 = (2*j+1)+1+1 by omega, gpow, gpow, h]
      apply Prod.ext <;> simp only [gmul] <;> grind only
    · rw [hA, hB, Int.natCast_succ]
      grind only
    · rw [hB]
      grind only

private theorem odd_real_dvd (z : Gaussian) (j : Nat) : z.1 ∣ (gpow z (2*j+1)).1 := by
  obtain ⟨A,_,_,_,_,h,_,_⟩ := odd_power_shape z.1 z.2 j
  rw [show z = (z.1,z.2) from rfl, h]
  exact Int.dvd_mul_right ..

/-- Raising to an odd power p gains a factor p in a real part divisible by p. -/
private theorem odd_power_gain (z : Gaussian) (p e : Nat) (odd : p%2 = 1)
    (h : (p:Int)^(e+1) ∣ z.1) : (p:Int)^(e+2) ∣ (gpow z p).1 := by
  obtain ⟨A,_,N,c,_,hz,hA,_⟩ := odd_power_shape z.1 z.2 (p/2)
  obtain ⟨t,ht⟩ := h
  have hp : (p:Int) = 2*((p/2 : Nat):Int)+1 := by omega
  rw [show z = (z.1,z.2) from rfl, show p = 2*(p/2)+1 by omega, hz]
  refine ⟨t*(N + (p:Int)^e*t*z.1*c), ?_⟩
  rw [Int.pow_succ] at ht
  rw [← show p = 2*(p/2)+1 by omega, Int.pow_succ, Int.pow_succ]
  change z.1*A = _
  rw [hA, ← hp]
  generalize (p:Int)^e = P at ht ⊢
  generalize z.1 = r at ht ⊢
  subst ht
  grind only

/-- If p divides the real part of z^d, the real part of z^(dk) is divisible by
one more power of p than the odd number k. -/
private theorem real_part_lift (z : Gaussian) (d p : Nat) (odd : p%2 = 1)
    (hd : (p:Int) ∣ (gpow z d).1) (e k : Nat) (hk : k%2 = 1) (he : p^e ∣ k) :
    (p:Int)^(e+1) ∣ (gpow z (d*k)).1 := by
  induction e generalizing k with
  | zero =>
    rw [show k = 2*(k/2)+1 by omega, gpow_mul]
    exact Int.dvd_trans (by simpa only [Nat.zero_add, Int.pow_one] using hd) (odd_real_dvd _ _)
  | succ e ih =>
    obtain ⟨m,rfl⟩ : ∃ m, k = m*p :=
      ⟨k/p, (Nat.div_mul_cancel (Nat.dvd_trans ⟨p^e, by rw [Nat.pow_succ, Nat.mul_comm]⟩ he)).symm⟩
    have hm : m%2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one m with h|h
      · rw [Nat.mul_mod, h] at hk
        simp at hk
      · exact h
    have hdiv : p^e ∣ m :=
      Nat.dvd_of_mul_dvd_mul_right (show 0 < p by omega) (by rwa [Nat.pow_succ] at he)
    rw [← Nat.mul_assoc, gpow_mul]
    exact odd_power_gain _ p e odd (ih m hm hdiv)

/-- A certificate that n + A Re(x^n) + B Re(y^n) has no zero among the odd
multiples of d: an odd p > 1, coprime to d, dividing the real parts of x^d and y^d.
The exponential part is then divisible by a higher power of p than the index. -/
theorem no_zero_on_odd_multiples (x y : Gaussian) (A B : Int) (d p : Nat)
    (odd : p%2 = 1) (big : 1 < p) (coprime : Nat.Coprime p d)
    (hx : (p:Int) ∣ (gpow x d).1) (hy : (p:Int) ∣ (gpow y d).1)
    (k : Nat) (hk : k%2 = 1) :
    ((d*k : Nat) : Int) + A*(gpow x (d*k)).1 + B*(gpow y (d*k)).1 ≠ 0 := by
  intro hz
  have all (e : Nat) : p^e ∣ k := by
    induction e with
    | zero => exact Nat.one_dvd k
    | succ e ih =>
      have a := real_part_lift x d p odd hx e k hk ih
      have b := real_part_lift y d p odd hy e k hk ih
      have eq : ((d*k : Nat) : Int) = -(A*(gpow x (d*k)).1 + B*(gpow y (d*k)).1) := by omega
      have dvd : p^(e+1) ∣ d*k := by
        apply Int.natCast_dvd_natCast.mp
        rw [Int.natCast_pow, eq]
        exact Int.dvd_neg.mpr (Int.dvd_add (Int.dvd_mul_of_dvd_right a) (Int.dvd_mul_of_dvd_right b))
      exact (Nat.Coprime.pow_left (e+1) coprime).dvd_of_dvd_mul_left dvd
  exact Nat.not_le.mpr (Nat.lt_pow_self big) (Nat.le_of_dvd (by omega) (all k))

/-- The two Gaussian bases agree modulo 3, so u_n ≡ n (mod 3). -/
private theorem value_mod_three (n : Nat) : value n % 3 = (n:Int)%3 := by
  have same (j : Nat) : ((powers j).a - (powers j).c)%3=0 ∧
      ((powers j).b - (powers j).d)%3=0 := by
    induction j with
    | zero => decide
    | succ j ih =>
      simp only [powers]
      obtain ⟨hr,hi⟩ := ih
      omega
  have hr := (same n).1
  unfold value
  omega

/-- The sequence has no zero. At a zero the index is an odd multiple of 12,
and 23 divides the real parts of both twelfth powers. -/
theorem no_zero (n : Nat) : frontier.term n ≠ 0 := by
  intro hz
  have h₂ := zero_index_mod n hz
  have hv : value n = 0 := (Rat.intCast_inj (b := 0)).mp ((term_eq_value n).symm.trans hz)
  have h₃ := value_mod_three n
  rw [hv] at h₃
  obtain ⟨ha,hb⟩ := powers_gaussian n
  have hn : n = 12*(2*(n/24)+1) := by omega
  have cert := no_zero_on_odd_multiples (-4,7) (8,1) 4 8 12 23 (by decide) (by decide)
    (by decide) (by decide) (by decide) (2*(n/24)+1) (by omega)
  rw [← hn, ← ha, ← hb] at cert
  exact cert hv

theorem frontier_has_no_zero : ¬ FrontierHasZero := fun ⟨n,hz⟩ => no_zero n hz

end Skolem.Research
