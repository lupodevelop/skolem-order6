import Frontier

namespace Skolem.Research

/-- Real and imaginary parts of the two Gaussian powers in the survey. -/
structure Powers where
  a : Int
  b : Int
  c : Int
  d : Int

def powers : Nat → Powers
  | 0 => ⟨1, 0, 1, 0⟩
  | n+1 =>
    let s := powers n
    ⟨-4*s.a-7*s.b, 7*s.a-4*s.b, 8*s.c-s.d, s.c+8*s.d⟩

def value (n : Nat) : Int := n + 4*(powers n).a + 8*(powers n).c

theorem value_recurrence (n : Nat) :
    value (n+6) = 10*value (n+5) - 19*value (n+4) + 532*value (n+3)
      - 5267*value (n+2) + 8970*value (n+1) - 4225*value n := by
  simp only [value, powers, Int.natCast_succ]
  omega

theorem term_eq_value (n : Nat) : frontier.term n = (value n : Rat) := by
  apply congrFun (frontier.sequence_unique (fun j => (value j : Rat)) ?_).symm
  constructor
  · exact of_decide_eq_true (by decide)
  · intro j
    change ((value (j+6) : Int) : Rat) =
      10*(value (j+5) : Rat) + (-19*(value (j+4) : Rat) + (532*(value (j+3) : Rat) +
      (-5267*(value (j+2) : Rat) + (8970*(value (j+1) : Rat) + (-4225*(value (j+0) : Rat) + 0)))))
    rw [value_recurrence]
    simp only [Rat.intCast_add, Rat.intCast_sub, Rat.intCast_mul]
    grind

private theorem four_step (n : Nat) :
    (powers (n+4)).a = -2047*(powers n).a - 3696*(powers n).b ∧
    (powers (n+4)).b = 3696*(powers n).a - 2047*(powers n).b ∧
    (powers (n+4)).c = 3713*(powers n).c - 2016*(powers n).d ∧
    (powers (n+4)).d = 2016*(powers n).c + 3713*(powers n).d := by
  simp only [powers]
  omega

private theorem four_invariant (m : Nat) :
    (powers (4*m)).a % 256 = 1 ∧ (powers (4*m)).b % 16 = 0 ∧
    (powers (4*m)).c % 128 = 1 ∧ (powers (4*m)).d % 32 = 0 := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [Nat.mul_succ]
    obtain ⟨ha,hb,hc,hd⟩ := four_step (4*m)
    obtain ⟨ia,ib,ic,id⟩ := ih
    rw [ha,hb,hc,hd]
    omega

theorem zero_index_mod (n : Nat) (hz : frontier.term n = 0) : n % 1024 = 1012 := by
  rw [term_eq_value] at hz
  have h : value n = 0 := (Rat.intCast_inj (b := 0)).mp hz
  unfold value at h
  have hn : n = 4*(n/4) := by omega
  obtain ⟨ha,_,hc,_⟩ := four_invariant (n/4)
  rw [← hn] at ha hc
  omega

end Skolem.Research
