import Skolem

set_option autoImplicit false

namespace Skolem.Research

/-- The order-six recurrence of Bacik et al., §8.3, equation (13). -/
def frontier : Instance where
  order := 6
  order_pos := by decide
  coeff := (#v[10, -19, 532, -5267, 8970, -4225] : Vector Rat 6).get
  initial := (#v[12, 49, 374, 6003, 21520, 150773] : Vector Rat 6).get
  last_coeff_ne_zero := by decide

abbrev FrontierHasZero : Prop := frontier.HasZero

#guard (List.range 8).map frontier.term == [12, 49, 374, 6003, 21520, 150773, 2711418, 7228087]

end Skolem.Research
