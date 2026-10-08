import Mathlib
import Submission.Work.ZassenhausSuzuki.CoreV2
import Submission.Work.ZassenhausSuzuki.mem_torus_of_conj
import Submission.Work.ZassenhausSuzuki.szA_of_isSuzukiTwoGroup
import Submission.Work.ZassenhausSuzuki.twoPoint_inverted
import Submission.Work.ZassenhausSuzuki.twoPoint_card_eq_center
import Submission.Work.ZassenhausSuzuki.three_le_of_odd_ringAut
import Submission.Work.ZassenhausSuzuki.range_conjAut_props
import Submission.Work.ZassenhausPSL2.ZData.three_le_card_twoPoint
import Submission.Work.ZassenhausPSL2.Feit.qomegaData_nonempty
import Submission.Work.ZassenhausTwoGroup.orbitData

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- **`SuzukiDataProp0`** from Higman's classification (`hHig`), Suzuki 1962 Lemma 6 (`h6`),
the `Q`-is-a-Suzuki-2-group input `hL3` and the cyclicity of `D = twoPoint H t` (`hL2`).

Route: `hL3` gives `IsSuzukiTwoGroup ↥Q` and `|Q| = |Z(Q)|²`, so Higman's classification
(`szA_of_isSuzukiTwoGroup`) coordinatises `Q` as `A(GF(2ⁿ), θ)` with `θ ≠ 1` of odd order;
`|D| + 1 = |Z(Q)| = 2ⁿ` (`twoPoint_card_add_one_eq_center_card`), whence `n ≥ 3`
(`three_le_of_odd_ringAut`).  The conjugation action `φ : D →* Aut Q`
(`Work.ZassenhausTwoGroup.conjAutDHom`, built from `H ≤ N_G(Q)`) is transported by the
coordinatisation to `Z'' = im(congr_{e₀} ∘ φ) ≤ Aut A(GF(2ⁿ),θ)`; `Z''` is cyclic of order
`2ⁿ - 1` and acts fixed point freely on the involutions (`range_conjAut_props`, from
`dStab_fpf_on_Q`), so Suzuki's Lemma 6 gives `Z'' = ψ Λ ψ⁻¹`.  Conjugating by `ψ` inside
`Aut A` and re-coordinatising by `e := ψ⁻¹ ∘ e₀` (`mem_torus_of_conj`) turns every `d ∈ D`
into a standard torus element `h_λ`. -/
theorem suzukiDataProp0 (hHig : Submission.Blueprint.HigmanProp)
    (h6 : Work.ZassenhausSuzuki.SuzukiLemma6Prop)
    (hL3 : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ (H Q : Subgroup G) (t : G),
      Submission.Blueprint.IsSplitRankOne H Q t → Submission.Blueprint.IsZassenhaus H →
      IsPGroup 2 Q → ¬ Submission.Blueprint.IsAbelianSubgroup Q →
      Submission.Blueprint.IsSuzukiTwoGroup ↥Q
        ∧ Nat.card ↥Q = Nat.card ↥(Subgroup.center ↥Q) ^ 2)
    (hL2 : ∀ (G : Type) [Group G] [Finite G] {H Q : Subgroup G} {t : G},
      Submission.Blueprint.IsSplitRankOne H Q t → Submission.Blueprint.IsZassenhaus H →
      IsPGroup 2 Q → Submission.Blueprint.HigmanProp →
      Submission.Blueprint.IsSuzukiTwoGroup ↥Q → IsCyclic ↥(Submission.Blueprint.twoPoint H t)) :
    Work.ZassenhausSuzuki.SuzukiDataProp0 := by
  intro G hGrp hFin hsimple H Q t hsplit hZass h2 hnab
  letI := hGrp
  letI := hFin
  haveI := hsimple
  -- (1) `Q` is a Suzuki 2-group of order `|Z(Q)|²` (input `hL3`).
  obtain ⟨hSuz, hcardQ⟩ := hL3 G hsimple H Q t hsplit hZass h2 hnab
  -- (2) Higman: `Q ≅ A(GF(2ⁿ), θ)`, `θ ≠ 1` of odd order, `|Z(Q)| = 2ⁿ`.
  obtain ⟨n, θ, hθ1, hθodd, hZn, he0⟩ := szA_of_isSuzukiTwoGroup hHig hSuz hcardQ
  obtain ⟨e0⟩ := he0
  -- (3) `Q ≠ ⊥` and `|D| + 1 = |Z(Q)| = 2ⁿ`.
  have hQne : Q ≠ ⊥ := Work.ZassenhausPSL2.Feit.Q_ne_bot_of_split hsplit
  have hDplus : Nat.card ↥(twoPoint H t) + 1 = 2 ^ n := by
    rw [twoPoint_card_add_one_eq_center_card hsplit hZass h2 hSuz, hZn]
  have hDge3 : 3 ≤ Nat.card ↥(twoPoint H t) :=
    Work.ZassenhausPSL2.ZData.three_le_card_twoPoint hsplit hZass
  -- (4) hence `n ≥ 3` (`n ≥ 2` from `|D| ≥ 3`, then the finite-field fact).
  have hn2 : 2 ≤ n := by
    have h4 : 4 ≤ 2 ^ n := by omega
    by_contra h
    push Not at h
    interval_cases n <;> norm_num at h4
  have hn3 : 3 ≤ n := three_le_of_odd_ringAut (m := n) (by omega) θ hθ1 hθodd
  -- (5) `D` is cyclic (input `hL2`) and `|D| = 2ⁿ - 1`.
  have hcyc : IsCyclic ↥(twoPoint H t) := hL2 G hsplit hZass h2 hHig hSuz
  have hDcard : Nat.card ↥(twoPoint H t) = 2 ^ n - 1 := by omega
  -- (6) the conjugation action `φ : D →* Aut Q`.
  let φ : ↥(twoPoint H t) →* MulAut ↥Q := Work.ZassenhausTwoGroup.conjAutDHom hsplit
  have hφ : ∀ (d : ↥(twoPoint H t)) (x : ↥Q),
      ((φ d x : ↥Q) : G) = (d : G) * (x : G) * (d : G)⁻¹ := by
    intro d x
    have h1 : φ d x = Work.ZassenhausTwoGroup.conjQD hsplit d x :=
      Work.ZassenhausTwoGroup.conjAutD_apply hsplit d x
    rw [h1, Work.ZassenhausTwoGroup.conjQD_coe]
  -- (7) the transported image `Z'' ≤ Aut (A(GF(2ⁿ),θ))` is cyclic of order `2ⁿ - 1` and
  -- acts fixed point freely on the involutions.
  obtain ⟨hcycZ, hcardZ, hfpfZ⟩ :=
    range_conjAut_props hsplit hZass hQne e0 φ hφ hcyc hDcard
  -- (8) Suzuki's Lemma 6: `Z'' = ψ Λ ψ⁻¹`.
  obtain ⟨ψ, hψ⟩ := h6 n θ hθ1 hθodd ((MulAut.congr e0).toMonoidHom.comp φ).range
    hcycZ hcardZ hfpfZ
  -- (9) assemble: re-coordinatise by `e := ψ⁻¹ ∘ e₀`; `mem_torus_of_conj` makes every
  -- `d ∈ D` act as a standard torus element `h_λ`.
  refine ⟨n, hn3, θ, hθ1, hθodd, e0.trans ψ.symm, ?_⟩
  intro d hd
  let d' : ↥(twoPoint H t) := ⟨d, hd⟩
  have hzmem : (MulAut.congr e0) (φ d')
      ∈ ((MulAut.congr e0).toMonoidHom.comp φ).range := ⟨d', rfl⟩
  obtain ⟨lam, hlam⟩ := mem_torus_of_conj (Z' := ((MulAut.congr e0).toMonoidHom.comp φ).range)
    (ψ := ψ) hψ ((MulAut.congr e0) (φ d')) hzmem
  refine ⟨lam, ?_⟩
  intro x
  refine ⟨φ d' x, hφ d' x, ?_⟩
  have hz : ((MulAut.congr e0) (φ d')) (e0 x) = e0 (φ d' x) := by
    show (e0.symm.trans ((φ d').trans e0)) (e0 x) = e0 (φ d' x)
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have h2 := hlam (ψ.symm (e0 x))
  simp only [MulEquiv.apply_symm_apply] at h2
  rw [hz] at h2
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  exact h2

end Work.ZassenhausSuzuki
