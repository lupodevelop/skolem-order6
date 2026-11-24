import NoZero

namespace Skolem.Research

private def addG (z w : Gaussian) : Gaussian := (z.1 + w.1, z.2 + w.2)
private def scaleG (c : Int) (z : Gaussian) : Gaussian := (c*z.1, c*z.2)
private def conjG (z : Gaussian) : Gaussian := (z.1, -z.2)

/-- Equation (13) of Bacik et al., section 8.3, with all four signed bases. -/
def survey13 (n : Nat) : Gaussian :=
  addG (addG (scaleG 2 (gpow (-4, 7) n)) (scaleG 2 (gpow (-4, -7) n)))
    (addG (addG (scaleG 4 (gpow (8, 1) n)) (scaleG 4 (gpow (8, -1) n))) (n, 0))

private theorem conj_power (z : Gaussian) (n : Nat) :
    gpow (conjG z) n = conjG (gpow z n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [gpow, ih, gpow]
    apply Prod.ext <;> simp [conjG, gmul] <;> grind only

/-- Conjugate pairs cancel in the imaginary coordinate at every index. -/
theorem survey13_eq_value (n : Nat) : survey13 n = (value n, 0) := by
  have ha := conj_power (-4, 7) n
  have hb := conj_power (8, 1) n
  change gpow (-4, -7) n = _ at ha
  change gpow (8, -1) n = _ at hb
  obtain ⟨hx,hy⟩ := powers_gaussian n
  unfold survey13
  rw [ha,hb,←hx,←hy]
  apply Prod.ext <;> simp only [value, addG, scaleG, conjG] <;> omega

theorem frontier_eq_survey13 (n : Nat) : frontier.term n = ((survey13 n).1 : Rat) := by
  rw [survey13_eq_value, term_eq_value]

theorem survey13_ne_zero (n : Nat) : survey13 n ≠ (0,0) := by
  intro hz
  apply no_zero n
  rw [frontier_eq_survey13, hz]
  rfl

end Skolem.Research
