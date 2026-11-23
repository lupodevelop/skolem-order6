import FrontierTerms

namespace Skolem.Research
abbrev Gaussian := Int × Int

def gmul (x y : Gaussian) : Gaussian :=
  (x.1*y.1-x.2*y.2, x.1*y.2+x.2*y.1)

def gpow (x : Gaussian) : Nat → Gaussian
  | 0 => (1,0)
  | n+1 => gmul (gpow x n) x

theorem gpow_add (x : Gaussian) (n m : Nat) :
    gpow x (n+m) = gmul (gpow x n) (gpow x m) := by
  induction m with
  | zero => simp [gpow,gmul]
  | succ m ih =>
    rw [Nat.add_succ,gpow,ih,gpow]
    apply Prod.ext <;> simp only [gmul] <;> grind only

theorem gpow_mul (x : Gaussian) (n m : Nat) : gpow x (n*m) = gpow (gpow x n) m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Nat.mul_succ,gpow_add,ih,gpow]

theorem powers_gaussian (n : Nat) :
    ((powers n).a,(powers n).b) = gpow (-4,7) n ∧
    ((powers n).c,(powers n).d) = gpow (8,1) n := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨ha,hb⟩ := ih
    simp only [powers,gpow,←ha,←hb,gmul,Prod.mk.injEq]
    omega

end Skolem.Research
