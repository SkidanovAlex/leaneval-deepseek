import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.HornParts
import Submission.Work.Interfaces.HornProper
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.germ_expansion_free
import Submission.Work.Horn.petal_components_upper_local
import Submission.Work.Horn.petal_spread_component
import Submission.Work.Horn.flower_petals_Dg
import Submission.Work.Horn.basin_components_infinite
import Submission.Work.Horn.spread_surj_on_component
import Submission.Work.Horn.germ_expansion_pushdown
import Submission.Work.Horn.petal_family_of_germ_expansion

namespace Work.Horn

/-!
# `Work.Horn.spreadDatum_and_basinDatum_of_componentStatement`

`SpreadDatum ∧ BasinDatum` for the pushed-down horn map `g = pushdown d.E` from the per-component
clause of Shishikura's Lemma 5.4 (`MandelDim.HornComponentStatement`).

* `Work.Horn.germ_expansion_pushdown` produces the Leau–Fatou expansion
  `g z = z + a z^(q+1) + o(z^(q+1))`, `q ≥ 1`, `a ≠ 0`, of the pushed-down horn map at `0`;
* `Work.Horn.petal_family_of_germ_expansion` produces the `q` pairwise disjoint, nonempty,
  `g`-invariant components of the parabolic basin `P` attached to that expansion, all contained in
  the bounded upper piece `{0} ∪ π '' (BuOf d B)`;
* `MandelDim.HornComponentStatement` then makes each of them an immediate basin of `g` on
  `D_g = insert 0 (π '' (Bu ∪ Bl))`, simply connected and carrying a critical point of `g`.

Conjunct 1 (`SpreadDatum`) is the pair `(q, a)` together with the family, its invariance, its
critical points and its pairwise disjointness; conjunct 2 (`BasinDatum`) is any single member of the
family (`q ≥ 1`), after cutting the rescaling `ζ ↦ s₀ ζ` of `Work.Horn.horn_germ_F0`.
-/

theorem spreadDatum_and_basinDatum_of_componentStatement
    (hobj : MandelDim.HornComponentStatement)
    (f₀ : ℂ → ℂ) (D₀ : Set ℂ) (hF0 : MandelDim.InF0 f₀ D₀) (d : MandelDim.ParabData f₀ D₀)
    {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B) (hBne : B.Nonempty)
    {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl) :
    Work.Horn.SpreadDatum (d := d) (η := η) (Bu := Bu) (Bl := Bl) ∧
      Work.Horn.BasinDatum (d := d) (η := η) (Bu := Bu) (Bl := Bl) := by
  obtain ⟨q, a, hq, ha, hgerm⟩ :=
    germ_expansion_pushdown hF0 d hB hBne hBu hBl hsub hup hlo
  obtain ⟨B', hcomp, hBuOf, hsubU, hmap, hdisj, _hne⟩ :=
    petal_family_of_germ_expansion hF0 d hB hBne hBu hBl hsub hup hlo hq ha hgerm
  obtain ⟨himm, hsc, hcrit⟩ :=
    hobj f₀ D₀ hF0 d hB hBne hBu hBl hsub hup hlo hcomp hBuOf
  refine ⟨⟨q, a, hq, ha, hgerm, B', hsubU, hmap, hcrit, hdisj⟩, ?_⟩
  exact ⟨B' ⟨0, by omega⟩, himm _, hsc _, hcrit _⟩

end Work.Horn
