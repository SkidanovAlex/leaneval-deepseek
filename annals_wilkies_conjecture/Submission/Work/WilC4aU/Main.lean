/-
  Area C4aU (Wilkie's conjecture for Pfaffian structures): the hole `C4a_uniform` of the C4a spec
  (`Submission/Work/Wilkies/CG/C4a/Spec.lean`).

  `PolyBoundedRExp` demands ONE finite set of exponents for the whole family; `h1` gives, for each
  parameter `c`, either eventual vanishing or an asymptotic `f_c (x) ~ a x ^ q`.  Uniformity is
  obtained from the cluster values of the ratio `f_c (2 x) / f_c (x)`, whose limit is `2 ^ (q c)`:

  * `ClusterSet Y` is existentially definable (`clusterFam_rexExist`, using `hR`; this is the
    definability content that the design routes through `C0_rexp_syntax` + `hR`, proved here
    directly from `hR`),
  * every cluster value is `2 ^ q` with `q : ℚ` (`clusterSet_countable`), so `ClusterSet Y` is
    countable,
  * countable + existentially definable ⊆ ℝ ⇒ finite (`finite_of_countable_rexExist`, which is
    uniform finiteness `hUF` at `k = 0`),
  * every occurring exponent `q` has `2 ^ q` in `ClusterSet Y` (`xSupp_eventually` +
    `ratioCluster_of_asymSect`), and `q ↦ 2 ^ q` is injective, so the occurring exponents are the
    finite set `expPreimage '' ClusterSet Y` (`exists_exponent_finset`).

  The main theorem is stated in the namespace of the hole (`WilkiesDesign.CG.C4a.C4a_uniform_proved`)
  and re-exported under the namespace of this area (`Work.WilC4aU.C4a_uniform_proved`).
-/
import Submission.Work.WilC4aU.Extract
import Submission.Work.WilC4aU.clusterFam_rexExist
import Submission.Work.WilC4aU.clusterSet_countable
import Submission.Work.WilC4aU.finite_of_countable_rexExist
import Submission.Work.WilC4aU.xSupp_eventually
import Submission.Work.WilC4aU.ratioCluster_of_asymSect

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
noncomputable section
open Classical Topology

namespace WilkiesDesign.CG.C4a

open WilkiesDesign (RExpExist)

/-- **C4a_uniform (the hole of the C4a spec).**  Restricted-exponential families are polynomially
bounded with rationally many exponents, uniformly in the parameters. -/
theorem C4a_uniform_proved
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hUF : UnifFiniteRExp)
    (h1 : ∀ (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)), RExpExist Y →
      (∀ (c : Fin k → ℝ) (x y y' : ℝ), Fin.cons x (Fin.cons y c) ∈ Y →
        Fin.cons x (Fin.cons y' c) ∈ Y → y = y') →
      ∀ c : Fin k → ℝ, PBOne Y c) :
    PolyBoundedRExp := by
  intro k Y hY hfun
  have h1c : ∀ c : Fin k → ℝ, PBOne Y c := h1 k Y hY hfun
  have hcnt : (Work.WilC4aU.ClusterSet Y).Countable := Work.WilC4aU.clusterSet_countable h1c
  have hfam : (Work.WilC4aU.ClusterFam Y).Finite :=
    Work.WilC4aU.finite_of_countable_rexExist hUF
      (Work.WilC4aU.clusterFam_rexExist Y hY hR)
      ((Work.WilC4aU.countable_clusterSet_iff Y).mp hcnt)
  have hfin : (Work.WilC4aU.ClusterSet Y).Finite := Work.WilC4aU.finite_clusterSet_of_fam hfam
  obtain ⟨Qs, hQs⟩ := Work.WilC4aU.exists_exponent_finset h1c
    (fun c q a hA hZ =>
      Work.WilC4aU.ratioCluster_of_asymSect hA (Work.WilC4aU.xSupp_eventually hUF hY hZ)) hfin
  exact ⟨Qs, hQs⟩

/-- Type check: `C4a_uniform_proved` has exactly the type of the frozen hole
`WilkiesDesign.CG.C4a.C4a_uniform` (see `HoleChk.lean` for the check against the hole itself). -/
example : (∀ (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hUF : UnifFiniteRExp)
    (h1 : ∀ (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)), RExpExist Y →
      (∀ (c : Fin k → ℝ) (x y y' : ℝ), Fin.cons x (Fin.cons y c) ∈ Y →
        Fin.cons x (Fin.cons y' c) ∈ Y → y = y') →
      ∀ c : Fin k → ℝ, PBOne Y c), PolyBoundedRExp) :=
  @C4a_uniform_proved

end WilkiesDesign.CG.C4a

namespace Work.WilC4aU

open WilkiesDesign (RExpExist)

/-- **C4a_uniform (area `WilC4aU`).**  The same statement, under the namespace of this area. -/
theorem C4a_uniform_proved
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hUF : WilkiesDesign.CG.UnifFiniteRExp)
    (h1 : ∀ (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)), RExpExist Y →
      (∀ (c : Fin k → ℝ) (x y y' : ℝ), Fin.cons x (Fin.cons y c) ∈ Y →
        Fin.cons x (Fin.cons y' c) ∈ Y → y = y') →
      ∀ c : Fin k → ℝ, WilkiesDesign.CG.C4a.PBOne Y c) :
    WilkiesDesign.CG.PolyBoundedRExp :=
  WilkiesDesign.CG.C4a.C4a_uniform_proved hR hUF h1

end Work.WilC4aU
