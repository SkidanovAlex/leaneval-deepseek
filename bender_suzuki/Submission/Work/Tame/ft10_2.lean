import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.Chapter10
import Submission.Work.Tame.Hyp
import Submission.Work.Tame.irr_vanishes_off_hatN
import Submission.Work.Tame.ft9_5
import Submission.Work.Tame.cfInner_tau_theta
import Submission.Work.Clifford.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Tame.ft10_2` — Feit–Thompson Lemma 10.2 (p. 814)

Assuming Hypothesis 10.2 for the supporting subgroup `𝔎_i` of the tamely imbedded set `L̂`, a
generalized character `Θ` of `𝔛` which is orthogonal to `𝓘₀(𝓢_α)^*` for every character `α` of
`𝔎_i` with `(α, 1_{𝔎_i}) = 0` is constant on the cosets of `𝔎_i` which lie in `𝔑_i − 𝔎_i`.

The proof follows Feit–Thompson.  Frobenius reciprocity converts the orthogonality hypothesis into
`⟨Θ|_{𝔑_i}, θ₁ − θ₂⟩ = 0` for all irreducible `θ₁, θ₂` of `𝔑_i` which agree on `𝔎_i` and whose
common restriction is orthogonal to the principal character.

Hypothesis 10.2 (in its faithful *one-way* form: every constituent of `Ind_{𝔎_i}^{𝔑_i} θ` has the
same degree `d` and the same multiplicity `m` — see `Submission/Work/Tame/Hyp.lean` and
`Submission/Work/TypeI/NOTES_FALSE_Hyp10_2.md`) is then used to determine `Θ|_{𝔑_i}` on the
cosets outside `𝔎_i`.  The irreducibles of `𝔑_i` are fibred by their **restriction** to `𝔎_i`
(Feit–Thompson's own grouping): for `χ ∈ Irr 𝔎_i`, `χ ≠ 1`, and `θ ∈ Irr 𝔑_i` with
`⟨Ind χ, θ⟩ ≠ 0`, Clifford's theorem gives

  `θ|_{𝔎_i} = ⟨Ind χ, θ⟩ · Σ_{χ' ∈ orbit χ} χ'`  (`ft10_2_res_of_ne`),

so the fibre of `θ` is exactly the support of `Ind χ`; on that support the coefficients of `Θ` are
constant (this is the orthogonality hypothesis in the form `hrest`), and the sum of the fibre is a
multiple of `Ind χ`, hence vanishes off `𝔎_i`.  The fibres whose members restrict to a character
with non-zero principal component contribute `0` because their members are constant on the cosets
of `𝔎_i` (`ft10_2_kernel`).

The previous version of this file fibred by *degree* (`ft10_2_frob`, `ft10_2_restrict`,
`ft10_2_degclass`), which needs the converse of Hypothesis 10.2 ("every irreducible of degree `d`
is a constituent") — strictly stronger than FT's hypothesis and false in FT's own setting.  Those
three private lemmas are superseded by `ft10_2_res_of_ne` and `ft10_2_support_sum`.  `ft10_2`,
`ft10_3`, `ft10_4`, `ft10_5` and `ft10_1` have unchanged statements; this proof needs only the
one-way form.
-/

noncomputable section

open Classical

namespace Work.Tame

/-- Precomposition of an irreducible `CharCore` character with a group isomorphism. -/
private lemma irr_precomp_mulEquiv_core {A B : Type*} [Group A] [Group B] [Fintype A] [Fintype B]
    (e : A ≃* B) {f : B → ℂ} (hf : f ∈ CharCore.Irr B) :
    (fun a => f (e a)) ∈ CharCore.Irr A := by
  have h1 : f ∈ Work.Clifford.Irr B := by
    rw [Work.Clifford.irr_eq_coherence, ← Work.CharCore.Irr_coe_eq_coherence]; exact hf
  have h2 : (fun a => f (e a)) ∈ Work.Clifford.Irr A :=
    Work.Clifford.irr_precomp_mulEquiv e h1
  rw [← Finset.mem_coe, Work.CharCore.Irr_coe_eq_coherence, ← Work.Clifford.irr_eq_coherence]
  exact h2

/-- `cfInner` is invariant under precomposition with a group isomorphism. -/
private lemma cfInner_precomp_mulEquiv {A B : Type*} [Group A] [Group B] [Fintype A] [Fintype B]
    (e : A ≃* B) (f g : B → ℂ) :
    Coherence.cfInner (fun a => f (e a)) (fun a => g (e a)) = Coherence.cfInner f g := by
  rw [Coherence.cfInner_apply, Coherence.cfInner_apply]
  have hcard : Fintype.card A = Fintype.card B := Fintype.card_congr e.toEquiv
  rw [hcard]
  congr 1
  exact Equiv.sum_comp e.toEquiv (fun x => f x * starRingEnd ℂ (g x))

/-! ## Namespace translations

The definitions `cfInner`, `resFun`, `indFun` and `orbitSum` are duplicated (with the same body)
in the namespaces `Work.Clifford`, `Work.CharCore`, `Work.Induction` and `Work.Coherence`; the
lemmas about them are therefore interchangeable, but `rw` matches heads syntactically.  The
following four wrappers restate the lemmas used below with the heads of the target goals. -/

private lemma starRingEnd_natCast' (n : ℕ) : starRingEnd ℂ (n : ℂ) = (n : ℂ) :=
  map_natCast (starRingEnd ℂ) n

private lemma cfInner_smul_left' {H : Type*} [Group H] [Fintype H] (c : ℂ) (f g : H → ℂ) :
    Coherence.cfInner (c • f) g = c * Coherence.cfInner f g :=
  Work.Clifford.cfInner_smul_left c f g

private lemma cfInner_orbitSum_eq_ite' {N : Type*} [Group N] [Fintype N] {K : Subgroup N}
    [K.Normal] {θ φ : K → ℂ} (hθ : θ ∈ Work.Clifford.Irr K)
    (hφ : φ ∈ Work.Clifford.Irr K) :
    Coherence.cfInner (Work.Clifford.orbitSum K θ) φ =
      (if φ ∈ Work.Clifford.charOrbit K θ then (1 : ℂ) else 0) :=
  Work.Clifford.cfInner_orbitSum_eq_ite hθ hφ

/-- **Clifford's theorem in the form used for Lemma 10.2.**  If `χ ≠ 1` is an irreducible
character of the normal subgroup `K` and `θ` is an irreducible character of `N` with
`⟨Ind_K^N χ, θ⟩ ≠ 0`, then

  `θ|_K = ⟨Ind_K^N χ, θ⟩ · Σ_{χ' ∈ orbit χ} χ'`

(so in particular `θ|_K` is a multiple of `orbitSum K χ`, with multiplicity the pairing of `θ`
with the induced character). -/
private lemma ft10_2_res_of_ne {N : Type*} [Group N] [Fintype N] {K : Subgroup N} [K.Normal]
    (mm : ↥(CharCore.Irr K) → ℕ)
    (hm : ∀ χ : ↥(CharCore.Irr K), (χ : K → ℂ) ≠ 1 →
        ∀ θ ∈ CharCore.Irr N,
          Coherence.cfInner (Induction.indFun K (χ : K → ℂ)) θ ≠ 0 →
          Coherence.cfInner (Induction.indFun K (χ : K → ℂ)) θ = (mm χ : ℂ))
    {χ : ↥(CharCore.Irr K)} (hχ : (χ : K → ℂ) ≠ 1) {θ : N → ℂ} (hθ : θ ∈ CharCore.Irr N)
    (hne : Coherence.cfInner (Induction.indFun K (χ : K → ℂ)) θ ≠ 0) :
    Induction.resFun K θ = (mm χ : ℂ) • Work.Clifford.orbitSum K (χ : K → ℂ) := by
  have hθc : θ ∈ Work.Clifford.Irr N := by
    rw [Work.Clifford.irr_eq_coherence, ← Work.CharCore.Irr_coe_eq_coherence]; exact hθ
  obtain ⟨θ', hθ', e, he, hres⟩ := Work.Clifford.clifford_decomposition (N := K) hθc
  have hχc : (χ : K → ℂ) ∈ Work.Clifford.Irr K := by
    rw [Work.Clifford.irr_eq_coherence, ← Work.CharCore.Irr_coe_eq_coherence]; exact χ.2
  -- `θ|_K` is `e` times the orbit sum of `θ'`; pair with `χ`
  have hpair : Coherence.cfInner (Induction.resFun K θ) (χ : K → ℂ)
      = (e : ℂ) * (if (χ : K → ℂ) ∈ Work.Clifford.charOrbit K θ' then (1 : ℂ) else 0) := by
    change Work.Clifford.cfInner (Work.Clifford.resFun K θ) (χ : K → ℂ)
      = (e : ℂ) * (if (χ : K → ℂ) ∈ Work.Clifford.charOrbit K θ' then (1 : ℂ) else 0)
    rw [hres, Work.Clifford.cfInner_smul_left,
      Work.Clifford.cfInner_orbitSum_eq_ite hθ' hχc]
  -- Hypothesis 10.2 turns the pairing into `mm χ`
  have hhyp : Coherence.cfInner (Induction.resFun K θ) (χ : K → ℂ) = (mm χ : ℂ) := by
    change CharCore.cfInner (Induction.resFun K θ) (χ : K → ℂ) = (mm χ : ℂ)
    rw [CharCore.cfInner_conj_symm, ← Induction.frobenius_reciprocity K (χ : K → ℂ) θ
      (CharCore.isClassFun_of_mem_Irr hθ)]
    have h2 : CharCore.cfInner (Induction.indFun K (χ : K → ℂ)) θ = (mm χ : ℂ) :=
      hm χ hχ θ hθ hne
    rw [h2, starRingEnd_natCast']
  have hmem : (χ : K → ℂ) ∈ Work.Clifford.charOrbit K θ' := by
    by_contra hc
    have hprod : Coherence.cfInner (Induction.resFun K θ) (χ : K → ℂ) = 0 := by
      rw [hpair, if_neg hc, mul_zero]
    have hconj : Coherence.cfInner (Induction.indFun K (χ : K → ℂ)) θ
        = starRingEnd ℂ (Coherence.cfInner (Induction.resFun K θ) (χ : K → ℂ)) := by
      change CharCore.cfInner (Induction.indFun K (χ : K → ℂ)) θ
        = starRingEnd ℂ (CharCore.cfInner (Induction.resFun K θ) (χ : K → ℂ))
      rw [Induction.frobenius_reciprocity K (χ : K → ℂ) θ (CharCore.isClassFun_of_mem_Irr hθ),
        CharCore.cfInner_conj_symm]
    exact hne (by rw [hconj, hprod]; simp)
  have heq : (e : ℂ) = (mm χ : ℂ) := by
    rw [hpair, if_pos hmem, mul_one] at hhyp
    exact hhyp
  have hresI : Induction.resFun K θ = (e : ℂ) • Work.Clifford.orbitSum K θ' := hres
  rw [hresI, heq]
  congr 1
  rw [Work.Clifford.orbitSum_eq_sum, Work.Clifford.orbitSum_eq_sum,
    ← Work.Clifford.charOrbit_eq_of_mem hmem]

/-- If `θ` is an irreducible character of `N` whose restriction to the normal subgroup `K`
contains the principal character of `K` (equivalently `K` is contained in `ker θ`), then `θ` is
constant on the `K`-cosets. -/
private lemma ft10_2_kernel {N : Type*} [Group N] [Fintype N] {K : Subgroup N} [K.Normal]
    {θ : N → ℂ} (hθ : θ ∈ CharCore.Irr N)
    (h1 : Coherence.cfInner (Induction.resFun K θ) (1 : K → ℂ) ≠ 0) :
    ∀ n : N, ∀ h : K, θ (n * (h : N)) = θ n := by
  have hθc : θ ∈ Work.Clifford.Irr N := by
    rw [Work.Clifford.irr_eq_coherence, ← Work.CharCore.Irr_coe_eq_coherence]; exact hθ
  obtain ⟨θ', hθ', e, he, hres⟩ := Work.Clifford.clifford_decomposition (N := K) hθc
  have h1c : Work.Clifford.cfInner (Work.Clifford.resFun K θ) (1 : K → ℂ) ≠ 0 := h1
  have hsmul : Work.Clifford.cfInner (Work.Clifford.resFun K θ) (1 : K → ℂ)
      = (e:ℂ) * Work.Clifford.cfInner (Work.Clifford.orbitSum K θ') (1 : K → ℂ) := by
    rw [hres, Work.Clifford.cfInner_smul_left]
  have hone : (1 : K → ℂ) ∈ Work.Clifford.Irr K := by
    rw [show (1 : K → ℂ) = Work.Clifford.principalChar K from rfl]
    exact Work.Clifford.principalChar_mem_Irr
  rw [hsmul, Work.Clifford.cfInner_orbitSum_eq_ite hθ' hone] at h1c
  have hmem : (1 : K → ℂ) ∈ Work.Clifford.charOrbit K θ' := by
    by_contra hc; exact h1c (by simp [hc])
  have hθ'one : θ' = (1 : K → ℂ) := by
    obtain ⟨g, hg⟩ := Work.Clifford.mem_charOrbit.mp hmem
    have h3 : Work.Clifford.conjFun K g⁻¹ (Work.Clifford.conjFun K g θ') = θ' := by
      rw [← Work.Clifford.conjFun_mul, mul_inv_cancel, Work.Clifford.conjFun_one]
    rw [hg] at h3
    have h4 : Work.Clifford.conjFun K g⁻¹ (1 : K → ℂ) = 1 := by
      ext k; simp [Work.Clifford.conjFun_apply]
    rw [h4] at h3
    exact h3.symm
  have horb : Work.Clifford.orbitSum K (1 : K → ℂ) = 1 := by
    ext k
    rw [Work.Clifford.orbitSum_eq_sum]
    have hchar : Work.Clifford.charOrbit K (1 : K → ℂ) = {(1 : K → ℂ)} := by
      ext φ
      rw [Work.Clifford.mem_charOrbit, Finset.mem_singleton]
      constructor
      · rintro ⟨g, hg⟩
        rw [← hg]; ext k; simp [Work.Clifford.conjFun_apply]
      · intro hφ; rw [hφ]; exact ⟨1, Work.Clifford.conjFun_one K _⟩
    rw [hchar, Finset.sum_singleton]
  have hconst : ∀ k : K, θ k = θ 1 := by
    intro k
    have hk : θ k = (e:ℂ) * Work.Clifford.orbitSum K θ' k := by
      have := congrFun hres k; simpa using this
    have hk1 : θ (1:N) = (e:ℂ) * Work.Clifford.orbitSum K θ' (1:K) := by
      have := congrFun hres (1:K); simpa using this
    rw [hk, hk1, hθ'one, horb]; simp
  obtain ⟨M, hM, hMχ⟩ := (CharCore.mem_Irr_iff_exists θ).mp hθ
  haveI := CharCore.isSimpleModule_of_mem_irrSubmodules M hM
  have hirr : (CharCore.submoduleRep M).IsIrreducible :=
    CharCore.isIrreducible_submoduleRep M inferInstance
  intro n h
  have hval : (CharCore.submoduleRep M).character (h : N)
      = (CharCore.submoduleRep M).character 1 := by
    rw [hMχ]; exact hconst h
  have hk : (CharCore.submoduleRep M) (h : N) = 1 :=
    CharCore.eq_one_of_character_eq_degree (CharCore.submoduleRep M) hirr h hval
  calc θ (n * (h : N)) = (CharCore.submoduleRep M).character (n * (h : N)) := by rw [hMχ]
    _ = LinearMap.trace ℂ ↥M ((CharCore.submoduleRep M) (n * (h : N))) := rfl
    _ = LinearMap.trace ℂ ↥M ((CharCore.submoduleRep M) n
          * (CharCore.submoduleRep M) (h : N)) := by rw [map_mul]
    _ = LinearMap.trace ℂ ↥M ((CharCore.submoduleRep M) n) := by rw [hk, mul_one]
    _ = (CharCore.submoduleRep M).character n := rfl
    _ = θ n := by rw [hMχ]

/-- If `θ` is an irreducible character of `N` whose restriction to `K` is orthogonal to the
principal character of `K`, then it has an irreducible constituent `χ ≠ 1` of `θ|_K` with
`⟨Ind_K^N χ, θ⟩ = mm χ ≠ 0`: take `χ` in the restriction of `θ` by Clifford's theorem; the
pairing is the multiplicity `e > 0` of `χ` in `θ|_K`, and Hypothesis 10.2 identifies it with
`mm χ`. -/
private lemma ft10_2_extract {N : Type*} [Group N] [Fintype N] {K : Subgroup N} [K.Normal]
    (mm : ↥(CharCore.Irr K) → ℕ)
    (hm : ∀ χ : ↥(CharCore.Irr K), (χ : K → ℂ) ≠ 1 →
        ∀ θ ∈ CharCore.Irr N,
          Coherence.cfInner (Induction.indFun K (χ : K → ℂ)) θ ≠ 0 →
          Coherence.cfInner (Induction.indFun K (χ : K → ℂ)) θ = (mm χ : ℂ))
    {θ : N → ℂ} (hθ : θ ∈ CharCore.Irr N)
    (h1 : Coherence.cfInner (Induction.resFun K θ) (1 : K → ℂ) = 0) :
    ∃ χ : ↥(CharCore.Irr K), (χ : K → ℂ) ≠ 1 ∧
      Coherence.cfInner (Induction.indFun K (χ : K → ℂ)) θ = (mm χ : ℂ) ∧ mm χ ≠ 0 := by
  have hθc : θ ∈ Work.Clifford.Irr N := by
    rw [Work.Clifford.irr_eq_coherence, ← Work.CharCore.Irr_coe_eq_coherence]; exact hθ
  obtain ⟨θ', hθ', e, he, hres⟩ := Work.Clifford.clifford_decomposition (N := K) hθc
  have hene : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  have hresC : Induction.resFun K θ = (e:ℂ) • Work.Clifford.orbitSum K θ' := hres
  have hone : (1 : K → ℂ) ∈ Work.Clifford.Irr K := by
    rw [show (1 : K → ℂ) = Work.Clifford.principalChar K from rfl]
    exact Work.Clifford.principalChar_mem_Irr
  have hite : CharCore.cfInner (Work.Clifford.orbitSum K θ') (1 : K → ℂ)
      = (if (1 : K → ℂ) ∈ Work.Clifford.charOrbit K θ' then 1 else 0) :=
    Work.Clifford.cfInner_orbitSum_eq_ite hθ' hone
  have hsmul : CharCore.cfInner (Induction.resFun K θ) (1 : K → ℂ)
      = (e:ℂ) * CharCore.cfInner (Work.Clifford.orbitSum K θ') (1 : K → ℂ) := by
    rw [hresC, CharCore.cfInner_smul_left]
  have h0 : CharCore.cfInner (Induction.resFun K θ) (1 : K → ℂ) = 0 := h1
  rw [hsmul, hite] at h0
  have hnotmem : (1 : K → ℂ) ∉ Work.Clifford.charOrbit K θ' := by
    intro hc
    have hif : (if (1 : K → ℂ) ∈ Work.Clifford.charOrbit K θ' then (1:ℂ) else 0) ≠ 0 := by
      simp [hc]
    exact (mul_ne_zero hene hif) h0
  have hθ'ne : θ' ≠ (1 : K → ℂ) := by
    intro hh
    apply hnotmem
    rw [hh]
    exact Work.Clifford.mem_charOrbit.mpr ⟨1, Work.Clifford.conjFun_one K _⟩
  have hθ'core : θ' ∈ CharCore.Irr K := by
    rw [← Finset.mem_coe, CharCore.Irr_coe_eq_coherence, ← Work.Clifford.irr_eq_coherence]
    exact hθ'
  have hselfC : CharCore.cfInner θ' (Work.Clifford.orbitSum K θ') = 1 := by
    have hself : Work.Clifford.cfInner θ' (Work.Clifford.orbitSum K θ') = 1 := by
      rw [Work.Clifford.cfInner_conj_symm, Work.Clifford.cfInner_orbitSum_eq_ite hθ' hθ']
      simp
    exact hself
  have hfr : CharCore.cfInner (Induction.indFun K θ') θ = (e:ℂ) := by
    rw [Induction.frobenius_reciprocity K θ' θ (CharCore.isClassFun_of_mem_Irr hθ)]
    have h2 : CharCore.cfInner θ' (Induction.resFun K θ)
        = (e:ℂ) * CharCore.cfInner θ' (Work.Clifford.orbitSum K θ') := by
      rw [hresC, CharCore.cfInner_smul_right]; simp
    rw [h2, hselfC, mul_one]
  have hfrC : Coherence.cfInner
      (Induction.indFun K ((⟨θ', hθ'core⟩ : ↥(CharCore.Irr K)) : K → ℂ)) θ = (e:ℂ) := hfr
  have hhm := hm ⟨θ', hθ'core⟩ hθ'ne θ hθ (by rw [hfrC]; exact hene)
  rw [hfrC] at hhm
  refine ⟨⟨θ', hθ'core⟩, hθ'ne, hfrC.trans hhm, ?_⟩
  intro hz
  exact hene (by rw [hhm, hz]; simp)

/-- The sum of the irreducible characters of `N` which are constituents of `Ind_K^N χ` is a
multiple of `Ind_K^N χ` (Hypothesis 10.2 supplies the common multiplicity `mm χ`). -/
private lemma ft10_2_support_sum {N : Type*} [Group N] [Fintype N] {K : Subgroup N} [K.Normal]
    (mm : ↥(CharCore.Irr K) → ℕ)
    (hm : ∀ χ : ↥(CharCore.Irr K), (χ : K → ℂ) ≠ 1 →
        ∀ θ ∈ CharCore.Irr N,
          Coherence.cfInner (Induction.indFun K (χ : K → ℂ)) θ ≠ 0 →
          Coherence.cfInner (Induction.indFun K (χ : K → ℂ)) θ = (mm χ : ℂ))
    (χ : ↥(CharCore.Irr K)) (hχ : (χ : K → ℂ) ≠ 1) :
    (mm χ : ℂ) • (∑ θ ∈ (CharCore.Irr N).filter
        (fun θ => Coherence.cfInner (Induction.indFun K (χ : K → ℂ)) θ ≠ 0), θ)
      = Induction.indFun K (χ : K → ℂ) := by
  have hpt : ∀ θ ∈ CharCore.Irr N,
      CharCore.cfInner (Induction.indFun K (χ : K → ℂ)) θ
        = (if Coherence.cfInner (Induction.indFun K (χ : K → ℂ)) θ ≠ 0
            then (mm χ : ℂ) else 0) := by
    intro θ hθ
    by_cases h : Coherence.cfInner (Induction.indFun K (χ : K → ℂ)) θ ≠ 0
    · rw [if_pos h, show CharCore.cfInner (Induction.indFun K (χ : K → ℂ)) θ = (mm χ : ℂ)
          from hm χ hχ θ hθ h]
    · rw [if_neg h, show CharCore.cfInner (Induction.indFun K (χ : K → ℂ)) θ = 0
          from not_not.mp h]
  have hR : Induction.indFun K (χ : K → ℂ)
      = ∑ θ ∈ CharCore.Irr N,
          (if Coherence.cfInner (Induction.indFun K (χ : K → ℂ)) θ ≠ 0
            then (mm χ : ℂ) • θ else 0) := by
    have hdec := CharCore.classFun_eq_sum_irr (Induction.isClassFun_indFun K (χ : K → ℂ))
    conv_lhs => rw [hdec]
    refine Finset.sum_congr rfl (fun θ hθ => ?_)
    rw [hpt θ hθ]
    by_cases h : Coherence.cfInner (Induction.indFun K (χ : K → ℂ)) θ ≠ 0 <;> simp [h]
  conv_rhs => rw [hR]
  rw [Finset.smul_sum, Finset.sum_filter]

/-- Abstract form of the argument: a class function on `N` whose coefficients along irreducible
characters are constant on the fibres of the restriction to the normal subgroup `K` is constant
on the cosets of `K`. -/
private theorem ft10_2_key {N : Type*} [Group N] [Fintype N] {K : Subgroup N} [hKN : K.Normal]
    {Φ : N → ℂ} (hΦ : CharCore.IsClassFun Φ)
    (mm : ↥(CharCore.Irr K) → ℕ)
    (hm : ∀ χ : ↥(CharCore.Irr K), (χ : K → ℂ) ≠ 1 →
        ∀ θ ∈ CharCore.Irr N,
          Coherence.cfInner (Induction.indFun K (χ : K → ℂ)) θ ≠ 0 →
          Coherence.cfInner (Induction.indFun K (χ : K → ℂ)) θ = (mm χ : ℂ))
    (hrest : ∀ θ₁ ∈ CharCore.Irr N, ∀ θ₂ ∈ CharCore.Irr N,
      Induction.resFun K θ₁ = Induction.resFun K θ₂ →
      Coherence.cfInner (Induction.resFun K θ₁) (1 : K → ℂ) = 0 →
      Coherence.cfInner Φ θ₁ = Coherence.cfInner Φ θ₂) :
    ∀ n : N, n ∉ K → ∀ h : K, Φ (n * ↑h) = Φ n := by
  intro n hnK h
  have hdec := CharCore.classFun_eq_sum_irr hΦ
  have hL : Φ (n * (h : N))
      = ∑ θ ∈ CharCore.Irr N, CharCore.cfInner Φ θ * θ (n * (h : N)) := by
    conv_lhs => rw [hdec]
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun θ _ => by rw [Pi.smul_apply, smul_eq_mul])
  have hR : Φ n = ∑ θ ∈ CharCore.Irr N, CharCore.cfInner Φ θ * θ n := by
    conv_lhs => rw [hdec]
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun θ _ => by rw [Pi.smul_apply, smul_eq_mul])
  rw [← sub_eq_zero, hL, hR, ← Finset.sum_sub_distrib]
  rw [show (∑ θ ∈ CharCore.Irr N,
        (CharCore.cfInner Φ θ * θ (n * (h : N)) - CharCore.cfInner Φ θ * θ n))
      = ∑ θ ∈ CharCore.Irr N,
          CharCore.cfInner Φ θ * (θ (n * (h : N)) - θ n) from
    Finset.sum_congr rfl (fun θ _ => by ring)]
  have hmap : ∀ θ ∈ CharCore.Irr N,
      Induction.resFun K θ ∈ (CharCore.Irr N).image (Induction.resFun K) :=
    fun θ hθ => Finset.mem_image.mpr ⟨θ, hθ, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun θ => CharCore.cfInner Φ θ * (θ (n * (h : N)) - θ n))]
  refine Finset.sum_eq_zero (fun α hα => ?_)
  obtain ⟨θ₀, hθ₀S, hθ₀res⟩ := Finset.mem_image.mp hα
  have hnhK : n * (h : N) ∉ K := by
    intro hc
    apply hnK
    have h1 : n = (n * (h : N)) * (h : N)⁻¹ := by group
    rw [h1]; exact K.mul_mem hc (K.inv_mem h.2)
  by_cases hcase : Coherence.cfInner (Induction.resFun K θ₀) (1 : K → ℂ) = 0
  · -- the fibre of `θ₀` is the support of `Ind χ₀` for a constituent `χ₀` of `θ₀|_K`
    obtain ⟨χ₀, hχ₀ne, hχ₀pair, hχ₀m⟩ := ft10_2_extract mm hm hθ₀S hcase
    have hmmne : (mm χ₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hχ₀m
    have hsupp : Coherence.cfInner (Induction.indFun K (χ₀ : K → ℂ)) θ₀ ≠ 0 := by
      rw [hχ₀pair]; exact hmmne
    have hχ₀irr : (χ₀ : K → ℂ) ∈ Work.Clifford.Irr K := by
      rw [Work.Clifford.irr_eq_coherence, ← Work.CharCore.Irr_coe_eq_coherence]; exact χ₀.2
    have h1irr : (1 : K → ℂ) ∈ Work.Clifford.Irr K := by
      rw [show (1 : K → ℂ) = Work.Clifford.principalChar K from rfl]
      exact Work.Clifford.principalChar_mem_Irr
    have hfrθ : ∀ (θ : N → ℂ), θ ∈ CharCore.Irr N →
        Coherence.cfInner (Induction.resFun K θ) (χ₀ : K → ℂ)
          = starRingEnd ℂ (Coherence.cfInner (Induction.indFun K (χ₀ : K → ℂ)) θ) := by
      intro θ hθ
      change CharCore.cfInner (Induction.resFun K θ) (χ₀ : K → ℂ)
        = starRingEnd ℂ (CharCore.cfInner (Induction.indFun K (χ₀ : K → ℂ)) θ)
      rw [CharCore.cfInner_conj_symm, ← Induction.frobenius_reciprocity K (χ₀ : K → ℂ) θ
        (CharCore.isClassFun_of_mem_Irr hθ)]
    have hres0 : Coherence.cfInner (Induction.resFun K θ₀) (χ₀ : K → ℂ) = (mm χ₀ : ℂ) := by
      rw [hfrθ θ₀ hθ₀S, hχ₀pair, starRingEnd_natCast']
    have hchar1 : Work.Clifford.charOrbit K (1 : K → ℂ) = {(1 : K → ℂ)} := by
      ext φ
      rw [Work.Clifford.mem_charOrbit, Finset.mem_singleton]
      constructor
      · rintro ⟨g, hg⟩
        rw [← hg]; ext k; simp [Work.Clifford.conjFun_apply]
      · intro hφ; rw [hφ]; exact ⟨1, Work.Clifford.conjFun_one K _⟩
    have hnotmem1 : (1 : K → ℂ) ∉ Work.Clifford.charOrbit K (χ₀ : K → ℂ) := by
      intro hc
      have h1 : (χ₀ : K → ℂ) ∈ Work.Clifford.charOrbit K (1 : K → ℂ) := by
        rw [Work.Clifford.charOrbit_eq_of_mem hc]
        exact Work.Clifford.theta_mem_charOrbit _
      rw [hchar1, Finset.mem_singleton] at h1
      exact hχ₀ne h1
    have hfib : (CharCore.Irr N).filter (fun θ => Induction.resFun K θ = α)
        = (CharCore.Irr N).filter
            (fun θ => Coherence.cfInner (Induction.indFun K (χ₀ : K → ℂ)) θ ≠ 0) := by
      ext θ
      rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨hθS, hθres⟩
        refine ⟨hθS, ?_⟩
        have heq : Induction.resFun K θ = Induction.resFun K θ₀ := by rw [hθres, hθ₀res]
        intro hz
        have h1 : Coherence.cfInner (Induction.resFun K θ) (χ₀ : K → ℂ) = 0 := by
          rw [hfrθ θ hθS, hz]; simp
        rw [heq, hres0] at h1
        exact hmmne h1
      · rintro ⟨hθS, hθne⟩
        refine ⟨hθS, ?_⟩
        rw [ft10_2_res_of_ne mm hm hχ₀ne hθS hθne, ← hθ₀res,
          ft10_2_res_of_ne mm hm hχ₀ne hθ₀S hsupp]
    rw [hfib]
    have hconst : ∀ θ ∈ (CharCore.Irr N).filter
        (fun θ => Coherence.cfInner (Induction.indFun K (χ₀ : K → ℂ)) θ ≠ 0),
        CharCore.cfInner Φ θ = CharCore.cfInner Φ θ₀ := by
      intro θ hθmem
      obtain ⟨hθS, hθne⟩ := Finset.mem_filter.mp hθmem
      refine hrest θ hθS θ₀ hθ₀S ?_ ?_
      · rw [ft10_2_res_of_ne mm hm hχ₀ne hθS hθne,
          ft10_2_res_of_ne mm hm hχ₀ne hθ₀S hsupp]
      · have hresθ : Induction.resFun K θ
            = (mm χ₀ : ℂ) • Work.Clifford.orbitSum K (χ₀ : K → ℂ) :=
          ft10_2_res_of_ne mm hm hχ₀ne hθS hθne
        rw [hresθ, cfInner_smul_left', cfInner_orbitSum_eq_ite' hχ₀irr h1irr, if_neg hnotmem1,
          mul_zero]
    have hstep : (∑ θ ∈ (CharCore.Irr N).filter
          (fun θ => Coherence.cfInner (Induction.indFun K (χ₀ : K → ℂ)) θ ≠ 0),
          CharCore.cfInner Φ θ * (θ (n * (h : N)) - θ n))
        = (∑ θ ∈ (CharCore.Irr N).filter
          (fun θ => Coherence.cfInner (Induction.indFun K (χ₀ : K → ℂ)) θ ≠ 0),
          CharCore.cfInner Φ θ₀ * (θ (n * (h : N)) - θ n)) :=
      Finset.sum_congr rfl (fun θ hθ => by rw [hconst θ hθ])
    rw [hstep, ← Finset.mul_sum]
    have hsumθ : (∑ θ ∈ (CharCore.Irr N).filter
        (fun θ => Coherence.cfInner (Induction.indFun K (χ₀ : K → ℂ)) θ ≠ 0), θ)
        = (mm χ₀ : ℂ)⁻¹ • Induction.indFun K (χ₀ : K → ℂ) := by
      have h := ft10_2_support_sum mm hm χ₀ hχ₀ne
      conv_rhs => rw [← h]
      rw [inv_smul_smul₀ hmmne]
    have hvanish : ∀ x : N, x ∉ K → Induction.indFun K (χ₀ : K → ℂ) x = 0 := by
      intro x hx
      apply Induction.indFun_apply_eq_zero
      intro y hy
      have hc := hKN.conj_mem (y * x * y⁻¹) hy y⁻¹
      have hc' : y⁻¹ * (y * x * y⁻¹) * y ∈ K := by simpa using hc
      rw [show y⁻¹ * (y * x * y⁻¹) * y = x from by group] at hc'
      exact hx hc'
    have hz₁ : (∑ θ ∈ (CharCore.Irr N).filter
          (fun θ => Coherence.cfInner (Induction.indFun K (χ₀ : K → ℂ)) θ ≠ 0),
          θ) (n * (h : N)) = 0 := by
      rw [hsumθ, Pi.smul_apply, hvanish _ hnhK, smul_zero]
    have hz₂ : (∑ θ ∈ (CharCore.Irr N).filter
          (fun θ => Coherence.cfInner (Induction.indFun K (χ₀ : K → ℂ)) θ ≠ 0),
          θ) n = 0 := by
      rw [hsumθ, Pi.smul_apply, hvanish _ hnK, smul_zero]
    have hsum2 : (∑ θ ∈ (CharCore.Irr N).filter
          (fun θ => Coherence.cfInner (Induction.indFun K (χ₀ : K → ℂ)) θ ≠ 0),
          (θ (n * (h : N)) - θ n)) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_apply, ← Finset.sum_apply, hz₁, hz₂, sub_self]
    rw [hsum2, mul_zero]
  · -- every member of the fibre is constant on the `K`-cosets
    have hzero : ∀ θ ∈ (CharCore.Irr N).filter (fun θ => Induction.resFun K θ = α),
        θ (n * (h : N)) = θ n := by
      intro θ hθmem
      obtain ⟨hθS, hθres⟩ := Finset.mem_filter.mp hθmem
      have hne0 : Coherence.cfInner (Induction.resFun K θ) (1 : K → ℂ) ≠ 0 := by
        rw [hθres, ← hθ₀res]; exact hcase
      exact ft10_2_kernel hθS hne0 n h
    exact Finset.sum_eq_zero (fun θ hθ => by rw [hzero θ hθ, sub_self, mul_zero])

/-- **Feit–Thompson Lemma 10.2** (p. 814).  Assume Hypothesis 10.2 for the supporting subgroup
`𝔎_i` of the tamely imbedded set `L̂`.  For a character `α` of `𝔎_i` let `𝓢_α` be the set of
irreducible characters of `𝔑_i = N(𝔎_i)` whose restriction to `𝔎_i` is `α` (here `θ|_𝔎_i` is
`hh ↦ θ ⟨hh, ·⟩`).  If `Θ` is a generalized character of `𝔛` which is orthogonal to `𝓘₀(𝓢_α)^*`
for every `α` with `(α, 1_{𝔎_i}) = 0` — formalised as: `⟨Θ, Ind_{𝔑_i}^{𝔛}(θ₁ - θ₂)⟩ = 0` for all
irreducible `θ₁, θ₂` of `𝔑_i` with common restriction `α` to `𝔎_i` and `⟨α, 1⟩ = 0` — then `Θ` is
constant on the cosets of `𝔎_i` which lie in `𝔑_i − 𝔎_i`, i.e. `Θ (N·H) = Θ N` for `N ∈ 𝔑_i`,
`N ∉ 𝔎_i`, `H ∈ 𝔎_i`.

Feit–Thompson's proof: the members of `𝓢_α` vanish on `𝔑_i − Ñ_i − 𝔎_i` (Lemma 4.3, as in
`irr_vanishes_off_hatN`); Frobenius reciprocity turns `⟨Θ, (θ₁ - θ₂)^*⟩ = 0` into
`⟨Θ|_{𝔑_i}, θ₁ - θ₂⟩ = 0`; Hypothesis 10.2 then gives `Θ|_{𝔑_i} = γ̃ + β` with `γ̃` induced
from `𝔎_i` and `β` a generalized character of `𝔑_i/𝔎_i`, so `Θ(N) = β(N)` for
`N ∈ 𝔑_i − 𝔎_i`, which is constant on the cosets of `𝔎_i`. -/
theorem ft10_2 {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} {i : Fin n} (h : Hyp10_2 Lhat n Hs i)
    {Θ : X → ℂ} (hΘ : CharCore.IsVChar Θ)
    (horth : ∀ α : ↥(Hs i) → ℂ, Coherence.cfInner α (1 : ↥(Hs i) → ℂ) = 0 →
      ∀ θ₁ ∈ CharCore.Irr ↥(Lgrp (Hs i : Set X)), ∀ θ₂ ∈ CharCore.Irr ↥(Lgrp (Hs i : Set X)),
        (∀ hh : ↥(Hs i), θ₁ ⟨(hh : X), (Hs i).le_normalizer hh.2⟩ = α hh) →
        (∀ hh : ↥(Hs i), θ₂ ⟨(hh : X), (Hs i).le_normalizer hh.2⟩ = α hh) →
        Coherence.cfInner Θ
          (Induction.indFun (Lgrp (Hs i : Set X)) (fun y => θ₁ y - θ₂ y)) = 0) :
    ∀ N : X, N ∈ Lgrp (Hs i : Set X) → N ∉ (Hs i : Set X) →
      ∀ H : X, H ∈ Hs i → Θ (N * H) = Θ N := by
  intro N hN hNK H hH
  let Nn : Subgroup X := Lgrp (Hs i : Set X)
  let K : Subgroup ↥Nn := (Hs i).subgroupOf Nn
  haveI hKN : K.Normal := by
    change ((Hs i).subgroupOf (Subgroup.normalizer ((Hs i) : Set X))).Normal
    infer_instance
  let Φ : ↥Nn → ℂ := Induction.resFun Nn Θ
  have hΦ : CharCore.IsClassFun Φ := Induction.isClassFun_resFun (H := Nn) hΘ.isClassFun
  let incl : ↥(Hs i) →* ↥Nn := Subgroup.inclusion (Subgroup.le_normalizer (H := Hs i))
  let ee : ↥K ≃* ↥(Hs i) := subEquiv (Hs i)
  have hrest : ∀ θ₁ ∈ CharCore.Irr ↥Nn, ∀ θ₂ ∈ CharCore.Irr ↥Nn,
      Induction.resFun K θ₁ = Induction.resFun K θ₂ →
      Coherence.cfInner (Induction.resFun K θ₁) (1 : K → ℂ) = 0 →
      Coherence.cfInner Φ θ₁ = Coherence.cfInner Φ θ₂ := by
    intro θ₁ hθ₁ θ₂ hθ₂ hres h1
    let α : ↥(Hs i) → ℂ := fun hh => θ₁ (incl hh)
    have hcomp : Induction.resFun K θ₁ = fun y : K => α (ee y) := by
      funext y
      simp only [Induction.resFun_apply, α]
      congr 1
    have hα0 : Coherence.cfInner α (1 : ↥(Hs i) → ℂ) = 0 := by
      have h1c : Coherence.cfInner (fun y : K => α (ee y)) (1 : K → ℂ) = 0 := by
        rw [← hcomp]; exact h1
      have h1c' : Coherence.cfInner (fun y : K => α (ee y))
          (fun y : K => (1 : ↥(Hs i) → ℂ) (ee y)) = 0 := by
        rwa [show (fun y : K => (1 : ↥(Hs i) → ℂ) (ee y)) = (1 : K → ℂ) from
          by funext y; simp]
      rwa [cfInner_precomp_mulEquiv ee α (1 : ↥(Hs i) → ℂ)] at h1c'
    have hΘ0 := horth α hα0 θ₁ hθ₁ θ₂ hθ₂ (fun hh => rfl) (fun hh => by
      have hk := congrFun hres (show K from ⟨incl hh, hh.2⟩)
      simp only [Induction.resFun_apply] at hk
      exact hk.symm)
    have hΘ0' : CharCore.cfInner (Induction.resFun Nn Θ) (fun y : ↥Nn => θ₁ y - θ₂ y) = 0 := by
      rw [← Induction.frobenius_reciprocity_transposed Nn Θ (fun y : ↥Nn => θ₁ y - θ₂ y)
        hΘ.isClassFun]
      exact hΘ0
    have hfin : CharCore.cfInner (Induction.resFun Nn Θ) θ₁
        = CharCore.cfInner (Induction.resFun Nn Θ) θ₂ := by
      have hthis := hΘ0'
      rw [show (fun y : ↥Nn => θ₁ y - θ₂ y) = θ₁ - θ₂ from rfl] at hthis
      rw [CharCore.cfInner_sub_right, sub_eq_zero] at hthis
      exact hthis
    exact hfin
  have hθθne : ∀ χ : ↥(CharCore.Irr K), (χ : K → ℂ) ≠ 1 →
      (fun hh : ↥(Hs i) => (χ : K → ℂ) (ee.symm hh)) ≠ 1 := by
    intro χ hχ hc
    apply hχ
    funext y
    have h1 : (fun hh : ↥(Hs i) => (χ : K → ℂ) (ee.symm hh)) (ee y)
        = (1 : ↥(Hs i) → ℂ) (ee y) := congrFun hc (ee y)
    simpa using h1
  have hfun : ∀ χ : ↥(CharCore.Irr K),
      (fun y : K => (χ : K → ℂ) (ee.symm ((subEquiv (Hs i)) y))) = (χ : K → ℂ) := by
    intro χ
    funext y
    rw [show subEquiv (Hs i) = ee from rfl]
    first | simp | (show (χ : K → ℂ) (ee.symm (ee y)) = (χ : K → ℂ) y; rw [ee.symm_apply_apply]) | exact congrArg _ (ee.symm_apply_apply y)
  let mm : ↥(CharCore.Irr K) → ℕ := fun χ =>
    if hχ : (χ : K → ℂ) = 1 then 0
    else Classical.choose (Classical.choose_spec (h.induced_homogeneous
      (fun hh : ↥(Hs i) => (χ : K → ℂ) (ee.symm hh))
      (irr_precomp_mulEquiv_core ee.symm χ.2) (hθθne χ hχ)))
  have hm : ∀ χ : ↥(CharCore.Irr K), (χ : K → ℂ) ≠ 1 →
      ∀ θ ∈ CharCore.Irr ↥Nn,
        Coherence.cfInner (Induction.indFun K (χ : K → ℂ)) θ ≠ 0 →
        Coherence.cfInner (Induction.indFun K (χ : K → ℂ)) θ = (mm χ : ℂ) := by
    intro χ hχ θ hθ hne0
    have hmm : mm χ = Classical.choose (Classical.choose_spec (h.induced_homogeneous
        (fun hh : ↥(Hs i) => (χ : K → ℂ) (ee.symm hh))
        (irr_precomp_mulEquiv_core ee.symm χ.2) (hθθne χ hχ))) := by
      simp only [mm]; rw [dif_neg hχ]
    have hspec := Classical.choose_spec (Classical.choose_spec (h.induced_homogeneous
      (fun hh : ↥(Hs i) => (χ : K → ℂ) (ee.symm hh))
      (irr_precomp_mulEquiv_core ee.symm χ.2) (hθθne χ hχ))) θ hθ
    rw [hmm]
    refine (hspec ?_).2
    rw [show Induction.indFun ((Hs i).subgroupOf (Lgrp ↑(Hs i)))
          (fun y => (χ : K → ℂ) (ee.symm ((subEquiv (Hs i)) y)))
        = Induction.indFun K (χ : K → ℂ) from by rw [hfun χ]]
    exact hne0
  let n' : ↥Nn := ⟨N, hN⟩
  have hn'K : n' ∉ K := by
    intro hc
    exact hNK (by simpa [n'] using Subgroup.mem_subgroupOf.mp hc)
  let h' : K := ⟨⟨H, (Hs i).le_normalizer hH⟩, hH⟩
  have hkey := ft10_2_key hΦ mm hm hrest n' hn'K h'
  calc Θ (N * H) = Φ (n' * ↑h') := rfl
    _ = Φ n' := hkey
    _ = Θ N := rfl

end Work.Tame
