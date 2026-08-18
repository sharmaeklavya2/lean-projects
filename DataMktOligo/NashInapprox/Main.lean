module

public import DataMktOligo.LinDataMkt.Revenue
public import DataMktOligo.NashInapprox.Instance
public import DataMktOligo.MuOpt.Constants
import DataMktOligo.NashInapprox.Bridge
import DataMktOligo.MuOpt.Main
import DataMktOligo.MuOpt.Cap
import Mathlib.Tactic.NormNum

/-!
# Main result: no approximate Nash equilibrium exists

Composing the bridge of `DataMktOligo.NashInapprox.Bridge` with the optimization
result `DataMktOligo.MuOpt.Main.cStar_le_μ`, we get that the two-seller instance admits no
`c`-approximate Nash equilibrium for **any** `c` below `c*`.
-/

namespace DataMktOligo.NashInapprox

open DataMktOligo.MuOpt
  (Constraints cStar μ cStar_le_μ cStar_le_cap)

variable {α β ν : ℝ}

/-- **Main result: the pricing game has no approximate equilibrium below `c*`.**

For any nonnegative prices `(p, q)` and any `c < c*`, the prices `![p, q]` are not a
`c`-approximate Nash equilibrium of the sellers' pricing game.

`c*` is the optimization bound `DataMktOligo.MuOpt.cStar`. (The `cap` used inside
`DataMktOligo.MuOpt.μ` to stand in for `∞` does not appear, since `c < c* ≤ cap`.) -/
public theorem no_approxNE (h : Constraints α β ν) {p q c : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hc : c < cStar α β ν) :
    ¬ LinDataMkt.IsApproxNE (inst h) ![p, q] c :=
  not_isApproxNE_of_lt_μ h hp hq
    (lt_of_lt_of_le hc (cStar_le_cap h))
    (lt_of_lt_of_le hc ((cStar_le_μ α β ν h hp hq).1))

end DataMktOligo.NashInapprox
