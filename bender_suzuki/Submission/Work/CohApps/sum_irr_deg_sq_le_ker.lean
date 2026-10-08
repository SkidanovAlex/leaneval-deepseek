import Mathlib
import Submission.Work.CohApps.Defs
import Submission.Work.CharCore.Main
import Submission.Work.CharCore.mem_Irr_iff_fdrep
import Submission.Work.CharCore.charKernel_subgroup
import Submission.Work.Clifford.gallagher_mul_inflate_irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The sum of squares of the degrees of the irreducibles trivial on a normal subgroup

For a finite group `G` and a normal subgroup `N ⊴ G`, the irreducible complex characters of `G`
whose kernel contains `N` are exactly the inflations of the irreducible characters of the
quotient `G ⧸ N`, and inflation preserves degrees.  Since the squares of the degrees of the
irreducible characters of a finite group sum to the order of the group, the characters of `G`
trivial on `N` contribute `|G ⧸ N| = [G : N]`:

`∑_{θ ∈ Irr G, N ≤ ker θ} θ(1)^2 = [G : N]`.

This is the main result `Work.CohApps.sum_irr_deg_sq_le_ker`.

## Contents

* `inflateFun_mem_Irr` : inflating an irreducible character of `G ⧸ N` is irreducible on `G`
  (the `χ = 1` case of Gallagher's theorem);
* `exists_irr_quotient_of_le_ker` : an irreducible character of `G` trivial on `N` descends to an
  irreducible character of `G ⧸ N` (the factorial-theoretic "deflation"); the proof factors the
  simple representation affording `χ` through the quotient via `Representation.ofQuotient`;
* `isIrreducible_of_comp_surjective` : simplicity of a representation is stable under pulling
  back along a surjection (used by the previous point);
* `inflateFun_injective`, `inflateFun_mem_charKernel`, `irrDeg_inflateFun`,
  `real_sum_irr_deg_sq` : elementary supporting lemmas.
-/

set_option linter.style.haveILetI false

noncomputable section

open Classical

namespace Work.CohApps

/-- **Simplicity is stable under pulling back along a surjection.**  If `f : G →* H` is onto and
the representation `σ.comp f` of `G` is irreducible, then `σ` is irreducible: the
`f`-invariance condition defining a subrepresentation of `σ.comp f` is, by surjectivity of `f`,
the same as the one defining a subrepresentation of `σ`. -/
theorem isIrreducible_of_comp_surjective {G H V : Type*} [Group G] [Group H]
    [AddCommGroup V] [Module ℂ V] (f : G →* H) (hf : Function.Surjective f)
    (σ : Representation ℂ H V) (h : Representation.IsIrreducible (σ.comp f)) :
    Representation.IsIrreducible σ := by
  let tc : Subrepresentation σ → Subrepresentation (σ.comp f) := fun S =>
    ⟨S.toSubmodule, fun g x hx => S.apply_mem_toSubmodule (f g) hx⟩
  let oc : Subrepresentation (σ.comp f) → Subrepresentation σ := fun S =>
    ⟨S.toSubmodule, fun k x hx => by
      obtain ⟨g, rfl⟩ := hf k
      exact S.apply_mem_toSubmodule g hx⟩
  have htc_bot : tc ⊥ = ⊥ := Subrepresentation.toSubmodule_injective rfl
  have htc_top : tc ⊤ = ⊤ := Subrepresentation.toSubmodule_injective rfl
  have hoc_bot : oc ⊥ = ⊥ := Subrepresentation.toSubmodule_injective rfl
  have hoc_top : oc ⊤ = ⊤ := Subrepresentation.toSubmodule_injective rfl
  have hoc_tc : ∀ S, oc (tc S) = S := fun S => Subrepresentation.toSubmodule_injective rfl
  have htc_oc : ∀ S, tc (oc S) = S := fun S => Subrepresentation.toSubmodule_injective rfl
  refine { toNontrivial := ?_, eq_bot_or_eq_top := fun S => ?_ }
  · obtain ⟨a, b, hab⟩ := exists_pair_ne (Subrepresentation (σ.comp f))
    exact ⟨oc a, oc b, fun hh => hab (by rw [← htc_oc a, ← htc_oc b, hh])⟩
  · rcases eq_bot_or_eq_top (tc S) with hS | hS
    · left
      have hh : oc (tc S) = oc ⊥ := by rw [hS]
      rwa [hoc_tc S, hoc_bot] at hh
    · right
      have hh : oc (tc S) = oc ⊤ := by rw [hS]
      rwa [hoc_tc S, hoc_top] at hh

/-- **Inflation preserves irreducibility.**  If `χ` is an irreducible character of `G ⧸ N`, then
`Work.Clifford.inflateFun N χ` (the pullback of `χ` along `QuotientGroup.mk' N`) is an
irreducible character of `G`.  This is the `χ = 1` case of Gallagher's theorem
(`Work.Clifford.gallagher_mul_inflate_irr`). -/
theorem inflateFun_mem_Irr {G : Type*} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    [Fintype (G ⧸ N)] {χ : G ⧸ N → ℂ} (hχ : χ ∈ Work.CharCore.Irr (G ⧸ N)) :
    Work.Clifford.inflateFun N χ ∈ Work.CharCore.Irr G := by
  have hβ : χ ∈ Work.Clifford.Irr (G ⧸ N) := (Work.Clifford.mem_Irr_charCore_iff').mpr hχ
  have hθ : Work.Clifford.principalChar N ∈ Work.Clifford.Irr N :=
    Work.Clifford.principalChar_mem_Irr
  have hχG : Work.Clifford.principalChar G ∈ Work.Clifford.Irr G :=
    Work.Clifford.principalChar_mem_Irr
  have hext : Work.Clifford.Extends N (Work.Clifford.principalChar G)
      (Work.Clifford.principalChar N) := rfl
  have h := Work.Clifford.gallagher_mul_inflate_irr (N := N) hθ hχG hext hβ
  have hpc : Work.Clifford.principalChar G * Work.Clifford.inflateFun N χ =
      Work.Clifford.inflateFun N χ := by
    ext g; simp [Work.Clifford.principalChar]
  rw [hpc] at h
  exact (Work.Clifford.mem_Irr_charCore_iff').mp h

/-- **Deflation of an irreducible character.**  An irreducible character `χ` of `G` whose kernel
contains `N` is the inflation of an irreducible character of the quotient `G ⧸ N`.

The representation `V` affording `χ` is trivial on `N` (an element of `N` has character value
`χ 1`, hence acts as the identity by `Work.CharCore.eq_one_of_trace_eq_finrank`), so it factors
through the quotient (`Representation.ofQuotient`); the descended representation is irreducible
because its subrepresentations are those of `V`. -/
theorem exists_irr_quotient_of_le_ker {G : Type*} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    [Fintype (G ⧸ N)] {χ : G → ℂ} (hχ : χ ∈ Work.CharCore.Irr G)
    (hN : (N : Set G) ⊆ Work.CharCore.charKernel χ) :
    ∃ χ' : G ⧸ N → ℂ, χ' ∈ Work.CharCore.Irr (G ⧸ N) ∧
      Work.Clifford.inflateFun N χ' = χ := by
  classical
  obtain ⟨V, hV, hVχ⟩ := (Work.CharCore.mem_Irr_iff_fdrep χ).mp hχ
  have htriv : ∀ n : N, V.ρ (n : G) = 1 := by
    intro n
    have hchar : V.character (n : G) = V.character 1 := by
      rw [hVχ]; exact hN n.2
    have htr : LinearMap.trace ℂ V.V (V.ρ (n : G)) = (Module.finrank ℂ V.V : ℂ) := by
      have h2 := hchar
      rw [FDRep.char_one] at h2
      exact h2
    have hpow : (V.ρ (n : G)) ^ (Fintype.card G) = 1 := by
      rw [← map_pow (V.ρ) (n : G) (Fintype.card G), pow_card_eq_one, map_one]
    exact Work.CharCore.eq_one_of_trace_eq_finrank (V.ρ (n : G)) Fintype.card_pos hpow htr
  letI : Representation.IsTrivial (V.ρ.comp N.subtype) := ⟨fun n => htriv n⟩
  let ρ' : Representation ℂ (G ⧸ N) V.V := Representation.ofQuotient V.ρ N
  have hfactor : V.ρ = ρ'.comp (QuotientGroup.mk' N) := by
    ext g x
    exact (Representation.ofQuotient_coe_apply V.ρ N g x).symm
  have hIrredV : Representation.IsIrreducible V.ρ := (Work.CharCore.fdRep_simple_iff V).mp hV
  have hIrredρ' : Representation.IsIrreducible ρ' := by
    apply isIrreducible_of_comp_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    rwa [← hfactor]
  refine ⟨(FDRep.of ρ').character, ?_, ?_⟩
  · exact (Work.CharCore.mem_Irr_iff_fdrep _).mpr
      ⟨FDRep.of ρ', (Work.CharCore.fdRep_simple_iff _).mpr hIrredρ', rfl⟩
  · funext g
    show (FDRep.of ρ').character (QuotientGroup.mk (s := N) g) = χ g
    rw [← hVχ]
    rfl

/-- The inflation `G ⧸ N → G` is injective on functions. -/
theorem inflateFun_injective {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    Function.Injective (Work.Clifford.inflateFun N) := by
  intro u v huv
  funext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact congrFun huv g

/-- The inflation of any function on `G ⧸ N` is trivial on `N`. -/
theorem inflateFun_mem_charKernel {G : Type*} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    [Fintype (G ⧸ N)] (χ : G ⧸ N → ℂ) :
    (N : Set G) ⊆ Work.CharCore.charKernel (Work.Clifford.inflateFun N χ) := by
  intro n hn
  show χ (QuotientGroup.mk (s := N) n) = χ (QuotientGroup.mk (s := N) 1)
  rw [(QuotientGroup.eq_one_iff n).mpr hn, QuotientGroup.mk_one]

/-- Inflation preserves the degree of an irreducible character. -/
theorem irrDeg_inflateFun {G : Type*} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    [Fintype (G ⧸ N)] {χ : G ⧸ N → ℂ} (hχ : χ ∈ Work.CharCore.Irr (G ⧸ N)) :
    Work.CharCore.irrDeg (Work.Clifford.inflateFun N χ) = Work.CharCore.irrDeg χ := by
  have h1 : ((Work.CharCore.irrDeg (Work.Clifford.inflateFun N χ) : ℂ))
      = ((Work.CharCore.irrDeg χ : ℂ)) := by
    rw [← Work.CharCore.irrDeg_spec (inflateFun_mem_Irr N hχ), ← Work.CharCore.irrDeg_spec hχ]
    congr 1
  exact Nat.cast_injective h1

/-- The sum of the squares of the degrees of the irreducible characters of a finite group, as a
real number: `∑ χ ∈ Irr H, χ(1)^2 = |H|`.  This is the real form of
`Work.CharCore.sum_irr_degree_sq`. -/
theorem real_sum_irr_deg_sq (H : Type*) [Group H] [Fintype H] :
    ∑ χ ∈ Work.CharCore.Irr H, (Work.CharCore.irrDeg χ : ℝ) ^ 2 = (Nat.card H : ℝ) := by
  have h := Work.CharCore.sum_irr_degree_sq (G := H)
  have hC : (∑ χ ∈ Work.CharCore.Irr H, ((Work.CharCore.irrDeg χ : ℂ)) ^ 2)
      = (Nat.card H : ℂ) := by
    rw [← h]
    exact Finset.sum_congr rfl fun χ hχ => by rw [Work.CharCore.irrDeg_spec hχ]
  apply Complex.ofReal_inj.mp
  rw [Complex.ofReal_sum]
  simp only [Complex.ofReal_pow]
  exact hC

/-- **The sum of squares of the degrees of the irreducible characters whose kernel contains a
normal subgroup `N` equals the index `[G : N]`.**  The irreducible characters of `G` trivial on
`N` are exactly the inflations of the irreducible characters of `G ⧸ N`, inflation being
injective and degree-preserving, so the sum is
`∑ ψ ∈ Irr (G ⧸ N), ψ(1)^2 = |G ⧸ N| = [G : N]`. -/
theorem sum_irr_deg_sq_le_ker {G : Type*} [Group G] [Fintype G] (N : Subgroup G) [N.Normal] :
    ∑ θ ∈ (Work.CharCore.Irr G).filter (fun θ => (N : Set G) ⊆ Work.CharCore.charKernel θ),
      (Work.CharCore.irrDeg θ : ℝ) ^ 2 = (N.index : ℝ) := by
  classical
  haveI : Fintype (G ⧸ N) := QuotientGroup.fintype N
  have hinj : Function.Injective (Work.Clifford.inflateFun N) := inflateFun_injective N
  have himage : ((Work.CharCore.Irr (G ⧸ N)).image (Work.Clifford.inflateFun N))
      = (Work.CharCore.Irr G).filter (fun θ => (N : Set G) ⊆ Work.CharCore.charKernel θ) := by
    apply Finset.ext
    intro θ
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      exact ⟨inflateFun_mem_Irr N hψ, inflateFun_mem_charKernel N ψ⟩
    · rintro ⟨hθ, hker⟩
      obtain ⟨ψ, hψ, hψeq⟩ := exists_irr_quotient_of_le_ker N hθ hker
      exact ⟨ψ, hψ, hψeq⟩
  rw [← himage, Finset.sum_image (fun a _ b _ h => hinj h)]
  rw [Finset.sum_congr rfl (fun ψ hψ => by rw [irrDeg_inflateFun N hψ])]
  rw [real_sum_irr_deg_sq (G ⧸ N), Subgroup.index_eq_card]

end Work.CohApps
