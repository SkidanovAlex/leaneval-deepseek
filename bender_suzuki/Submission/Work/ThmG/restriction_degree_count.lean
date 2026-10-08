import Mathlib
import Submission.Work.ThmG.Defs
import Submission.Work.CharCore.Main
import Submission.Work.Induction.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

/-!
# `Work.ThmG.restriction_degree_count`

The degree count used in the proof of Peterfalvi II, Théorème G: if `f ∈ Irr G` restricts to
`H` with multiplicities proportional to a character `χ₀ ∈ Irr H` on a set `F ⊆ Irr H`,

  `⟨Res_H^G f, χ⟩_H = A χ * ⟨Res_H^G f, χ₀⟩_H`  for `χ ∈ F`,

then the common multiplicity `b = ⟨Res_H^G f, χ₀⟩_H` is a natural number and

  `b * ∑_{χ ∈ F} A χ * deg χ ≤ deg f`.

The mathematics is the expansion of the class function `Res_H^G f` at the identity in the
orthonormal basis `Irr H`: `f 1 = ∑_{χ ∈ Irr H} m χ * χ 1` with `m χ = ⟨Res_H^G f, χ⟩_H ∈ ℕ`
(`exists_nat_cfInner_resFun`), and the terms indexed by `F` are all non-negative.

## A note on the `Fintype` instance of `↥H`

`Work.Induction.exists_nat_cfInner_resFun` is stated with `{H : Subgroup G}` and
`θ ∈ Work.CharCore.Irr ↥H`, so the `Fintype ↥H` instance occurring there is *not* a binder: it
was resolved when that lemma was elaborated and is baked into its type (to the canonical
subtype instance).  The present file has an explicit `[Fintype ↥H]` binder, whose instance can
be an arbitrary one.  The lemma `exists_nat_cfInner_resFun_fintype` below repeats the same
argument with `[Fintype ↥H]` as a genuine binder, so that it applies with the instance at hand;
this is the only place where the identity of the instance matters, all other lemmas used
(`Work.CharCore.classFun_eq_sum_irr`, `Work.CharCore.irrDeg_spec`, …) carry `[Fintype G]`
as a binder and therefore pick up the ambient instance.
-/

namespace Work.ThmG

/-- **The multiplicity of an irreducible character of `H` in the restriction of an irreducible
character of `G` is a natural number**, stated with an explicit `[Fintype ↥H]` binder (compare
`Work.Induction.exists_nat_cfInner_resFun`, whose `Fintype ↥H` instance is fixed).

`⟨Res_H^G χ, θ⟩_H = |H|⁻¹ ∑_h χ h * conj (θ h)` is the dimension of the space of intertwining
maps between the restriction of the representation affording `χ` and the representation
affording `θ` (Mathlib's `Representation.card_inv_mul_sum_char_mul_char_eq_finrank`). -/
theorem exists_nat_cfInner_resFun_fintype {G : Type} [Group G] [Fintype G]
    {H : Subgroup G} [Fintype ↥H] {χ : G → ℂ} (hχ : χ ∈ Work.CharCore.Irr G)
    {θ : ↥H → ℂ} (hθ : θ ∈ Work.CharCore.Irr ↥H) :
    ∃ n : ℕ, Work.CharCore.cfInner (Work.Induction.resFun H χ) θ = (n : ℂ) := by
  classical
  -- write `χ` and `θ` as characters of simple submodules of the respective regular modules
  obtain ⟨N, _hN, hNχ⟩ := Work.CharCore.exists_mem_irrSubmodules_of_mem_Irr hχ
  obtain ⟨M, _hM, hMθ⟩ := Work.CharCore.exists_mem_irrSubmodules_of_mem_Irr hθ
  let ρ' : Representation ℂ ↥H ↥N := (Work.CharCore.submoduleRep N).comp H.subtype
  let σ : Representation ℂ ↥H ↥M := Work.CharCore.submoduleRep M
  have hρ' : Representation.character ρ' = Work.Induction.resFun H χ := by
    funext h
    change Representation.character (Work.CharCore.submoduleRep N) (h : G) = χ h
    rw [hNχ]
  have hσ : Representation.character σ = θ := hMθ
  -- the answer is the dimension of the space of intertwining maps
  refine ⟨Module.finrank ℂ (Representation.IntertwiningMap ρ' σ), ?_⟩
  have key := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ' σ
  rw [Work.CharCore.cfInner_apply]
  have hcard : (Fintype.card ↥H : ℂ) = (Nat.card ↥H : ℂ) := by
    rw [Fintype.card_eq_nat_card]
  rw [hcard]
  have hsum : ∑ x : ↥H, Work.Induction.resFun H χ x * starRingEnd ℂ (θ x)
      = ∑ x : ↥H, Representation.character σ x * Representation.character ρ' x⁻¹ := by
    rw [← Equiv.sum_comp (Equiv.inv ↥H)
      (fun x => Representation.character σ x * Representation.character ρ' x⁻¹)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← hρ', ← hσ, Work.CharCore.star_char σ x]
    simp only [Equiv.inv_apply, inv_inv]
    ring
  rw [hsum]
  exact key

theorem restriction_degree_count {G : Type} [Group G] [Fintype G]
    {H : Subgroup G} [Fintype ↥H]
    (F : Finset (↥H → ℂ)) (hF : ∀ χ ∈ F, χ ∈ Work.CharCore.Irr ↥H)
    {χ₀ : ↥H → ℂ} (hχ₀ : χ₀ ∈ F)
    (A : (↥H → ℂ) → ℕ) (hA : ∀ χ ∈ F, χ 1 = (A χ : ℂ) * χ₀ 1)
    {f : G → ℂ} (hf : f ∈ Work.CharCore.Irr G)
    (hmult : ∀ χ ∈ F, Work.CharCore.cfInner (Work.Induction.resFun H f) χ
        = (A χ : ℂ) * Work.CharCore.cfInner (Work.Induction.resFun H f) χ₀) :
    ∃ b : ℕ, Work.CharCore.cfInner (Work.Induction.resFun H f) χ₀ = (b : ℂ) ∧
      b * (∑ χ ∈ F, A χ * Work.CharCore.irrDeg χ) ≤ Work.CharCore.irrDeg f := by
  classical
  -- `Res_H^G f` is a class function on `H`.
  have hcfH : Work.CharCore.IsClassFun (Work.Induction.resFun H f) :=
    Work.Induction.isClassFun_resFun (Work.CharCore.isClassFun_of_mem_Irr hf)
  -- the multiplicity of `θ ∈ Irr H` in `Res_H^G f`, as a natural number
  let m : ↥(Work.CharCore.Irr ↥H) → ℕ := fun θ =>
    Classical.choose (exists_nat_cfInner_resFun_fintype (G := G) (H := H) hf θ.2)
  have hm : ∀ θ : ↥(Work.CharCore.Irr ↥H),
      Work.CharCore.cfInner (Work.Induction.resFun H f) (θ : ↥H → ℂ) = (m θ : ℂ) := fun θ =>
    Classical.choose_spec (exists_nat_cfInner_resFun_fintype (G := G) (H := H) hf θ.2)
  -- the same multiplicity extended by `0` off `Irr H`
  let mm : (↥H → ℂ) → ℕ := fun χ =>
    if h : χ ∈ Work.CharCore.Irr ↥H then m ⟨χ, h⟩ else 0
  have hmm : ∀ χ (hχ : χ ∈ Work.CharCore.Irr ↥H),
      (mm χ : ℂ) = Work.CharCore.cfInner (Work.Induction.resFun H f) χ := by
    intro χ hχ
    rw [show mm χ = m ⟨χ, hχ⟩ from dite_eq_left hχ]
    exact (hm ⟨χ, hχ⟩).symm
  -- the expansion of `Res_H^G f`, evaluated at `1`
  have hexp1 : (f 1 : ℂ) = (∑ χ ∈ Work.CharCore.Irr ↥H,
      (Work.CharCore.cfInner (Work.Induction.resFun H f) χ) • χ) (1 : ↥H) := by
    simpa using congr_fun (Work.CharCore.classFun_eq_sum_irr hcfH) (1 : ↥H)
  -- consequently the degree of `f` is the sum of the degrees of `Irr H` weighted by `mm`
  have hkey : Work.CharCore.irrDeg f
      = ∑ χ ∈ Work.CharCore.Irr ↥H, mm χ * Work.CharCore.irrDeg χ := by
    refine (Nat.cast_inj (R := ℂ)).mp ?_
    rw [Nat.cast_sum]
    simp only [Nat.cast_mul]
    rw [← Work.CharCore.irrDeg_spec hf, hexp1, Finset.sum_apply]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [Pi.smul_apply, smul_eq_mul, ← hmm χ hχ, Work.CharCore.irrDeg_spec hχ]
  -- on `F` the multiplicities are the prescribed multiples of the multiplicity of `χ₀`
  have hmmF : ∀ χ (hχ : χ ∈ F), mm χ = A χ * mm χ₀ := by
    intro χ hχ
    refine (Nat.cast_inj (R := ℂ)).mp ?_
    rw [Nat.cast_mul, hmm χ (hF χ hχ), hmult χ hχ, ← hmm χ₀ (hF χ₀ hχ₀)]
  refine ⟨mm χ₀, (hmm χ₀ (hF χ₀ hχ₀)).symm, ?_⟩
  -- the partial sum over `F` is bounded by the total sum
  have hsum_eq : mm χ₀ * (∑ χ ∈ F, A χ * Work.CharCore.irrDeg χ)
      = ∑ χ ∈ F, mm χ * Work.CharCore.irrDeg χ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hmmF χ hχ]
    ring
  rw [hsum_eq, hkey]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => hF x hx)
    (fun x _ _ => Nat.zero_le _)

end Work.ThmG
