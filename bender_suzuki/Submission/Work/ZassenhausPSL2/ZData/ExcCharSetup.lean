import Mathlib
import Submission.Work.ZassenhausPSL2.ZData.ExcCharDefs
import Submission.Work.Coherence.All
import Submission.Work.CharCore.Coherence
import Submission.Work.Clifford.All
import Submission.Work.BrauerSuzuki.TI.cfInner_indFun_eq_of_TISet
import Submission.Work.Induction.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Set-up for the T.I.F.N. exceptional-character lemma

Vocabulary and elementary group-theoretic facts for the proof of
`Work.ZassenhausPSL2.exc_char_coherent`: `K` is an abelian T.I.F.N. subgroup of a finite group `W`
(a T.I. set with `C_W(k) ≤ K` for `1 ≠ k ∈ K`), `N = N_W(K)`, and `𝒮 = {χ ∈ Irr N | K ⊄ ker χ}`.

The main statements are

* `Work.ZassenhausPSL2.centralizer_eq` — `C_W(k) = K` for `1 ≠ k ∈ K`;
* `Work.ZassenhausPSL2.isTISet` — `K \ {1}` is a TI set with normalizer `N` in the sense of
  Dade (`Work.BrauerSuzuki.IsTISet`);
* `Work.ZassenhausPSL2.mem_scriptS` — membership in `𝒮`.

**Instances.** `Submission.Blueprint.excludingKernel` builds the `Fintype` instance of the
subgroup it works with from the *ambient* `Fintype`; to keep statement and goal in sync, the
lemmas below are stated with `[Fintype W]` only and let instance search derive the subgroup
instances.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ZassenhausPSL2

open Classical

noncomputable section

variable {W : Type} [Group W] [Fintype W]

/-- The normalizer `N_W(K)`. -/
abbrev nrm (K : Subgroup W) : Subgroup W := Subgroup.normalizer (K : Set W)

/-- `K` viewed as a subgroup of `N_W(K)`. -/
abbrev Kn (K : Subgroup W) : Subgroup ↥(nrm K) := K.subgroupOf (nrm K)

/-- Peterfalvi's set `𝒮 = {χ ∈ Irr N_W(K) | K ⊄ ker χ}` (the characters of the normalizer of
`K` that do not contain `K` in their kernel). -/
abbrev scriptS (K : Subgroup W) : Finset (↥(nrm K) → ℂ) :=
  Submission.Blueprint.excludingKernel (nrm K) K

/-- `Ind_{N_W(K)}^W` as a `ℤ`-linear map on class functions. -/
abbrev indLinK (K : Subgroup W) : (↥(nrm K) → ℂ) →ₗ[ℤ] (W → ℂ) :=
  Submission.Blueprint.indLinear (nrm K)

/-- **The canonical `Fintype` instance on `↥(N_W K)`**, the one instance search produces from the
ambient `Fintype W` (and hence the one used internally by
`Submission.Blueprint.excludingKernel`).  Keeping a *named* copy lets a proof work at this
instance even in a context where another instance for `↥(N_W K)` is in scope. -/
noncomputable def instNrm (K : Subgroup W) : Fintype ↥(nrm K) := inferInstance

variable (K : Subgroup W)

/-- `K ≤ N_W(K)`. -/
lemma le_nrm : K ≤ nrm K := Subgroup.le_normalizer

/-- `K` is normal in `N_W(K)`. -/
lemma kn_normal (K : Subgroup W) : (Kn K).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (le_nrm K)).mpr le_rfl

/-- `K` is normal in `N_W(K)`, as an instance. -/
instance (K : Subgroup W) : (Kn K).Normal := kn_normal K

/-- **`C_W(k) = K` for `1 ≠ k ∈ K`.**  This is the "F" of T.I.F.N.: every non-identity element
of `K` is self-centralising (the hypothesis `hcent` gives `≤`, and commutativity of `K` gives
`≥`). -/
lemma centralizer_eq (hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K)
    {k : W} (hk : k ∈ K) (hk1 : k ≠ 1) : Subgroup.centralizer ({k} : Set W) = K := by
  refine le_antisymm (hcent k hk hk1) ?_
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hKcomm y hy k hk

/-- Membership in `𝒮`. -/
lemma mem_scriptS {χ : ↥(nrm K) → ℂ} :
    χ ∈ scriptS K ↔
      χ ∈ Work.CharCore.Irr ↥(nrm K) ∧
        ∃ x : ↥(nrm K), (x : W) ∈ K ∧ χ x ≠ χ 1 := by
  exact Finset.mem_filter (s := Work.CharCore.Irr ↥(nrm K)) (a := χ)
    (p := fun (ψ : ↥(nrm K) → ℂ) => ∃ x : ↥(nrm K), (x : W) ∈ K ∧ ψ x ≠ ψ 1)

/-- `𝒮 ⊆ Irr N`. -/
lemma scriptS_subset_Irr : ↑(scriptS K) ⊆ Work.CharCore.Irr ↥(nrm K) := by
  intro χ hχ
  exact ((mem_scriptS K).mp hχ).1

/-- **`K \ {1}` is a TI set with normalizer `N_W(K)`** (Dade's set form), for a TI subgroup `K`
with `C_W(k) ≤ K` for `1 ≠ k ∈ K`. -/
lemma isTISet (hTI : ∀ g : W, g ∉ nrm K → K ⊓ Submission.Blueprint.conj g K = ⊥)
    (hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K) :
    Work.BrauerSuzuki.IsTISet ((K : Set W) \ {1}) (nrm K) where
  one_notMem := by simp
  subset := by
    intro x hx
    exact le_nrm K (by simpa using hx.1)
  inv_mem := by
    rintro x ⟨hxK, hx1⟩
    refine ⟨K.inv_mem hxK, ?_⟩
    simp only [Set.mem_singleton_iff] at hx1 ⊢
    exact inv_ne_one.mpr hx1
  mem_normalizer := by
    rintro h hh x ⟨hxK, hx1⟩
    have hconj : h * x * h⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hh x).mp hxK
    refine ⟨hconj, ?_⟩
    simp only [Set.mem_singleton_iff] at hx1 ⊢
    intro hc
    exact hx1 (by
      calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
        _ = 1 := by rw [hc]; group)
  normalizer_le := by
    rintro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      by_cases h1 : h = 1
      · subst h1; simp
      · exact (hg ⟨hh, by simpa [Set.mem_singleton_iff] using h1⟩).1
    · intro hh
      by_cases h1 : h = 1
      · simpa [h1] using K.one_mem
      · have hψ_exists : ∀ x : ↥K, (if (x : W) = 1 then 1 else g * (x : W) * g⁻¹) ∈ K := by
          intro x
          by_cases hx : (x : W) = 1
          · simp [hx]
          · simp only [hx, if_false]
            exact (hg ⟨x.2, by simpa [Set.mem_singleton_iff] using hx⟩).1
        let ψ : ↥K → ↥K := fun x => ⟨_, hψ_exists x⟩
        have hψ_val : ∀ x : ↥K, ((ψ x : ↥K) : W) = g * (x : W) * g⁻¹ := by
          intro x
          by_cases hx : (x : W) = 1
          · dsimp only [ψ]
            rw [if_pos hx, hx]
            group
          · dsimp only [ψ]
            rw [if_neg hx]
        have hinj : Function.Injective ψ := by
          intro x y hxy
          have hv : g * (x : W) * g⁻¹ = g * (y : W) * g⁻¹ := by
            rw [← hψ_val x, ← hψ_val y, hxy]
          exact Subtype.ext (by
            have hc := congrArg (fun z => g⁻¹ * z * g) hv
            simpa [mul_assoc] using hc)
        have hsurj : Function.Surjective ψ := (Finite.injective_iff_surjective).mp hinj
        obtain ⟨x, hx⟩ := hsurj ⟨g * h * g⁻¹, hh⟩
        have hxval : g * (x : W) * g⁻¹ = g * h * g⁻¹ := by
          rw [← hψ_val x, hx]
        have hxh : (x : W) = h := by
          have hc := congrArg (fun z => g⁻¹ * z * g) hxval
          simpa [mul_assoc] using hc
        rw [← hxh]; exact x.2
  conj_disjoint := by
    rintro g hg x y ⟨hxK, hx1⟩ ⟨hyK, hy1⟩ hconj
    -- `x = g⁻¹ y g ∈ K ⊓ g⁻¹ K g`, and `g⁻¹ ∉ N_W(K)`
    have hginv : g⁻¹ ∉ nrm K := fun h => hg (by simpa using (nrm K).inv_mem h)
    have hxmem : x ∈ K ⊓ Submission.Blueprint.conj g⁻¹ K := by
      refine ⟨hxK, ?_⟩
      rw [Submission.Blueprint.conj]
      refine Subgroup.mem_map.mpr ⟨y, hyK, ?_⟩
      change (MulAut.conj g⁻¹) y = x
      rw [MulAut.conj_apply]
      rw [← hconj]; group
    rw [hTI g⁻¹ hginv, Subgroup.mem_bot] at hxmem
    exact hx1 (by simpa [Set.mem_singleton_iff] using hxmem)

end

end Work.ZassenhausPSL2
