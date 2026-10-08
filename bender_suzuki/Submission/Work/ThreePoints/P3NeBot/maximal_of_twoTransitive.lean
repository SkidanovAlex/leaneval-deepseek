import Mathlib
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.Basic
import Submission.Work.ThreePoints.Omega
import Submission.Work.DoubleTransitivity.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.P3NeBot

/-- An element of `N_G(X)` carries fixed points of `X` to fixed points of `X` (here for the
action of `G` on `Ω = G ⧸ H`).  Equivalently: the normaliser of `X` preserves `Ω_X`. -/
lemma smul_mem_fixedPts_of_mem_normalizer {G : Type} [Group G] {H X : Subgroup G} {f : G}
    (hf : f ∈ Subgroup.normalizer (X : Set G)) {ω : G ⧸ H}
    (hω : ω ∈ Submission.Blueprint.fixedPts H X) :
    f • ω ∈ Submission.Blueprint.fixedPts H X := by
  intro x hx
  have h1 : f⁻¹ * x * f ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp hf) (f⁻¹ * x * f)
    rw [show f * (f⁻¹ * x * f) * f⁻¹ = x from by group] at this
    exact this.mpr hx
  calc x • (f • ω) = (x * f) • ω := by rw [mul_smul]
    _ = (f * (f⁻¹ * x * f)) • ω := by rw [show x * f = f * (f⁻¹ * x * f) from by group]
    _ = f • ((f⁻¹ * x * f) • ω) := by rw [mul_smul]
    _ = f • ω := by rw [hω (f⁻¹ * x * f) h1]

/-- The canonical point `H` of `Ω = G ⧸ H` is fixed by `g` exactly when `g ∈ H`. -/
lemma smul_pt_eq_pt_iff {G : Type} [Group G] {H : Subgroup G} {g : G} :
    g • Work.DoubleTransitivity.pt H = Work.DoubleTransitivity.pt H ↔ g ∈ H := by
  rw [Work.DoubleTransitivity.smul_pt]
  exact Work.DoubleTransitivity.mk_one_eq_iff

/-- In a `2`-transitive action on `Ω_X = fixedPts H X` (`|Ω_X| ≥ 3`), a point stabiliser `F ⊓ H` is a maximal subgroup of `F` (this is the hypothesis `IsCoatom (stabilizer F a)` of Peterfalvi I Appendix III, needed when App. III (1) is applied to `F = p3F X` acting on `Ω_X`).

`hFN : F ≤ N_G(X)` is what makes `F` preserve `Ω_X`. Route: if `F ⊓ H < M ≤ F`, pick `m ∈ M ∖ (F ⊓ H)`; then `m` moves the point `H`; for every `c ∈ Ω_X` with `c ≠ H`, 2-transitivity gives `f ∈ F` with `f • H = H` and `f • (m • H) = c`, and `f ∈ F ⊓ H ≤ M`, so `c = (f m) • H ∈ M • H`; hence `M` is transitive on `Ω_X` with point stabiliser `M ⊓ H = F ⊓ H`, so `|M| = |Ω_X| · |F ⊓ H| = |F|` (both `F` and `M` are transitive on `Ω_X`), whence `M = F`. -/
theorem maximal_of_twoTransitive {G : Type} [Group G] [Finite G]
    {H F M X : Subgroup G}
    (hXH : X ≤ H) (hFN : F ≤ Subgroup.normalizer (X : Set G))
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    (h2t : Work.DoubleTransitivity.IsTwoTransitiveOnSub F (Submission.Blueprint.fixedPts H X))
    (hHM : F ⊓ H ≤ M) (hMF : M ≤ F) :
    M = F ⊓ H ∨ M = F := by
  classical
  rcases eq_or_ne M (F ⊓ H) with h | h
  · exact Or.inl h
  right
  refine le_antisymm hMF ?_
  -- `M` strictly contains the point stabiliser `F ⊓ H`, so it has an element `m ∉ H`.
  have hlt : ¬ M ≤ F ⊓ H := fun hle => h (le_antisymm hle hHM)
  rw [SetLike.le_def, not_forall] at hlt
  obtain ⟨m, hm⟩ := hlt
  rw [not_imp] at hm
  obtain ⟨hmM, hmNotH⟩ := hm
  have hmF : m ∈ F := hMF hmM
  have hmH : m ∉ H := fun hh => hmNotH (Subgroup.mem_inf.mpr ⟨hmF, hh⟩)
  -- the base point `pt H` and its image `m • pt H` lie in `Ω_X` and are distinct.
  have haS : Work.DoubleTransitivity.pt H ∈ Submission.Blueprint.fixedPts H X :=
    (Work.DoubleTransitivity.pt_mem_fixedPts_iff X H).mpr hXH
  have hma : m • Work.DoubleTransitivity.pt H ≠ Work.DoubleTransitivity.pt H := fun hh =>
    hmH (smul_pt_eq_pt_iff.mp hh)
  have hmS : m • Work.DoubleTransitivity.pt H ∈ Submission.Blueprint.fixedPts H X :=
    smul_mem_fixedPts_of_mem_normalizer (hFN hmF) haS
  -- now show `F ≤ M`
  intro f hfF
  by_cases hfH : f ∈ H
  · -- `f` already lies in the point stabiliser, hence in `M`
    exact hHM (Subgroup.mem_inf.mpr ⟨hfF, hfH⟩)
  · -- `f` moves the base point; 2-transitivity fixes `pt H` and carries `m • pt H` to `f • pt H`
    have hfa : f • Work.DoubleTransitivity.pt H ≠ Work.DoubleTransitivity.pt H := fun hh =>
      hfH (smul_pt_eq_pt_iff.mp hh)
    have hfS : f • Work.DoubleTransitivity.pt H ∈ Submission.Blueprint.fixedPts H X :=
      smul_mem_fixedPts_of_mem_normalizer (hFN hfF) haS
    obtain ⟨f', hf'F, hf'a, hf'e⟩ :=
      h2t (Work.DoubleTransitivity.pt H) haS (m • Work.DoubleTransitivity.pt H) hmS
        (Ne.symm hma) (Work.DoubleTransitivity.pt H) haS
        (f • Work.DoubleTransitivity.pt H) hfS (Ne.symm hfa)
    have hf'H : f' ∈ H := smul_pt_eq_pt_iff.mp hf'a
    have hf'M : f' ∈ M := hHM (Subgroup.mem_inf.mpr ⟨hf'F, hf'H⟩)
    have hg : f' * m ∈ M := M.mul_mem hf'M hmM
    -- `f⁻¹ * (f' * m)` fixes `pt H`, hence lies in `F ⊓ H ≤ M`; with `f' * m ∈ M` this gives `f ∈ M`.
    have hstab : f⁻¹ * (f' * m) ∈ H := by
      apply smul_pt_eq_pt_iff.mp
      calc (f⁻¹ * (f' * m)) • Work.DoubleTransitivity.pt H
          = f⁻¹ • ((f' * m) • Work.DoubleTransitivity.pt H) := by rw [mul_smul]
        _ = f⁻¹ • (f' • (m • Work.DoubleTransitivity.pt H)) := by rw [mul_smul]
        _ = f⁻¹ • (f • Work.DoubleTransitivity.pt H) := by rw [hf'e]
        _ = (f⁻¹ * f) • Work.DoubleTransitivity.pt H := by rw [mul_smul]
        _ = Work.DoubleTransitivity.pt H := by rw [inv_mul_cancel, one_smul]
    have hmemF : f⁻¹ * (f' * m) ∈ F := F.mul_mem (F.inv_mem hfF) (F.mul_mem hf'F hmF)
    have hmemM : f⁻¹ * (f' * m) ∈ M := hHM (Subgroup.mem_inf.mpr ⟨hmemF, hstab⟩)
    have hfinv : f⁻¹ ∈ M := by
      have : f⁻¹ = (f⁻¹ * (f' * m)) * (f' * m)⁻¹ := by group
      rw [this]
      exact M.mul_mem hmemM (M.inv_mem hg)
    simpa using M.inv_mem hfinv

end Work.ThreePoints.P3NeBot
