/-
# The Cartesian product of vanishing filtrations (the paper's Lemma `commutation`)

For finite-dimensional subspaces `V ⊆ ℝ⟦x_i⟧_{i∈σ}` and `W ⊆ ℝ⟦y_j⟧_{j∈τ}` of multivariate power
series, let `V ⊗ W ⊆ ℝ⟦x,y⟧` be the span of the products `u(x)·v(y)`.  This module proves the
paper's Lemma `commutation` — the Cartesian-product compatibility of the vanishing filtration
jumps (the paper's Corollary `jumps Cartesian` is the iteration of this lemma to `d` factors,
combined with the evaluation-module formalism of the paper's §"Filtered evaluation modules"):

`𝒱(V ⊗ W) = 𝒱(V) × 𝒱(W)`,

i.e. the leading exponents of the product space are exactly the pairs of leading exponents of `V`
and `W` (`jumpSet_prodSpace`).

The two-variable ring is `MvPowerSeries (σ ⊕ₗ τ) ℝ` (the index type is the *linear* sum `σ ⊕ₗ τ`,
so that `Lex ((σ ⊕ₗ τ) →₀ ℕ)` orders the σ-exponents before the τ-exponents), and

* `pairExp e f = x^e y^f` is the exponent `mapDomain Sum.inlₗ e + mapDomain Sum.inrₗ f`, with
  `comapInl`, `comapInr` its two projections (`pairExp_comap`, `comapInl_pairExp`,
  `comapInr_pairExp`, and the evaluation lemmas `pairExp_apply_inl/inr`);
* `renameInl`, `renameInr` embed the two rings (`MvPowerSeries.rename` along the inclusions), and
  `genVW V W`, `prodSpace V W` are the generator and the product space;
* `coeff_prod` is the **coefficient formula**
  `coeff μ (u(x)·v(y)) = coeff (comapInl μ) u · coeff (comapInr μ) v`, proved from the antidiagonal
  description of `coeff_mul` (the `Finsupp.comapDomain`/`mapDomain` round trip) — this is the
  "coefficient extraction" that drives both inclusions;
* `mem_prodSpace_iff` characterises the product space as the finite sums of products
  (`Finsupp.range_linearCombination`);
* `dk_pairExp_lt_iff`/`dk_pairExp_le`/`dk_pairExp_lt_left`/`dk_pairExp_lt_right` are the order
  calculus of `pairExp` w.r.t. the degree-lex key `dk` (using
  `Commons.Data.Finsupp.lex_mapDomain_lexSum_lt_iff`);
* `jumpSet_subset_prodSpace` is the inclusion `𝒱(V)·𝒱(W) ⊆ 𝒱(V ⊗ W)` (the product of two leading
  exponents is a leading exponent), and `exists_pair_leadExp_sum` (with `coeff_extract_sigma`,
  `coeff_extract_tau`, `coeff_extract_left`, `coeff_extract_right`) is the converse inclusion
  `𝒱(V ⊗ W) ⊆ 𝒱(V)·𝒱(W)` (the extraction of a `V`-element and a `W`-element from the coefficient
  at the leading exponent).
-/
import Mathlib
import Submission.CDT.MvVanishing
import Submission.CDT.MvVanishingCount
import Submission.Commons.Data.Finsupp.lex_mapDomain_lexSum_lt_iff

open MvPowerSeries
open scoped BigOperators

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

namespace Submission.CDT.MvVanishing

variable {σ τ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
  [Fintype τ] [DecidableEq τ] [LinearOrder τ]

/-! ## The basic two-variable exponent calculus -/

theorem inlₗ_inj {a b : σ} (h : (Sum.inlₗ a : σ ⊕ₗ τ) = Sum.inlₗ b) : a = b :=
  Sum.inl.inj (toLex.injective h)

theorem inrₗ_inj {a b : τ} (h : (Sum.inrₗ a : σ ⊕ₗ τ) = Sum.inrₗ b) : a = b :=
  Sum.inr.inj (toLex.injective h)

theorem inlₗ_ne_inrₗ (a : σ) (b : τ) : (Sum.inlₗ a : σ ⊕ₗ τ) ≠ Sum.inrₗ b :=
  fun h => Sum.inl_ne_inr (toLex.injective h)

theorem inrₗ_ne_inlₗ (b : τ) (a : σ) : (Sum.inrₗ b : σ ⊕ₗ τ) ≠ Sum.inlₗ a :=
  fun h => Sum.inr_ne_inl (toLex.injective h)

abbrev inlEmb : σ ↪ σ ⊕ₗ τ := ⟨Sum.inlₗ, fun _ _ h => inlₗ_inj h⟩

abbrev inrEmb : τ ↪ σ ⊕ₗ τ := ⟨Sum.inrₗ, fun _ _ h => inrₗ_inj h⟩

noncomputable def pairExp (e : σ →₀ ℕ) (f : τ →₀ ℕ) : (σ ⊕ₗ τ) →₀ ℕ :=
  Finsupp.mapDomain Sum.inlₗ e + Finsupp.mapDomain Sum.inrₗ f

noncomputable def comapInl (μ : (σ ⊕ₗ τ) →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.comapDomain (Sum.inlₗ : σ → σ ⊕ₗ τ) μ (fun _ _ _ _ h => inlₗ_inj h)

noncomputable def comapInr (μ : (σ ⊕ₗ τ) →₀ ℕ) : τ →₀ ℕ :=
  Finsupp.comapDomain (Sum.inrₗ : τ → σ ⊕ₗ τ) μ (fun _ _ _ _ h => inrₗ_inj h)

theorem pairExp_apply_inl (e : σ →₀ ℕ) (f : τ →₀ ℕ) (a : σ) :
    pairExp e f (Sum.inlₗ a) = e a := by
  have h1 : pairExp e f (Sum.inlₗ a) =
      (Finsupp.mapDomain Sum.inlₗ e : (σ ⊕ₗ τ) →₀ ℕ) (Sum.inlₗ a)
        + (Finsupp.mapDomain Sum.inrₗ f : (σ ⊕ₗ τ) →₀ ℕ) (Sum.inlₗ a) := by
    simp only [pairExp, Finsupp.add_apply]
  have h2 : (Finsupp.mapDomain Sum.inrₗ f : (σ ⊕ₗ τ) →₀ ℕ) (Sum.inlₗ a) = 0 :=
    Finsupp.mapDomain_of_notMem_range (f := Sum.inrₗ) f (Sum.inlₗ a) (by
      rintro ⟨b, hb⟩; exact inrₗ_ne_inlₗ b a hb)
  have h3 : (Finsupp.mapDomain Sum.inlₗ e : (σ ⊕ₗ τ) →₀ ℕ) (Sum.inlₗ a) = e a :=
    Finsupp.mapDomain_apply_of_injective inlEmb.injective e a
  rw [h1, h2, h3, add_zero]

theorem pairExp_apply_inr (e : σ →₀ ℕ) (f : τ →₀ ℕ) (b : τ) :
    pairExp e f (Sum.inrₗ b) = f b := by
  have h1 : pairExp e f (Sum.inrₗ b) =
      (Finsupp.mapDomain Sum.inlₗ e : (σ ⊕ₗ τ) →₀ ℕ) (Sum.inrₗ b)
        + (Finsupp.mapDomain Sum.inrₗ f : (σ ⊕ₗ τ) →₀ ℕ) (Sum.inrₗ b) := by
    simp only [pairExp, Finsupp.add_apply]
  have h2 : (Finsupp.mapDomain Sum.inlₗ e : (σ ⊕ₗ τ) →₀ ℕ) (Sum.inrₗ b) = 0 :=
    Finsupp.mapDomain_of_notMem_range (f := Sum.inlₗ) e (Sum.inrₗ b) (by
      rintro ⟨a, ha⟩; exact inlₗ_ne_inrₗ a b ha)
  have h3 : (Finsupp.mapDomain Sum.inrₗ f : (σ ⊕ₗ τ) →₀ ℕ) (Sum.inrₗ b) = f b :=
    Finsupp.mapDomain_apply_of_injective inrEmb.injective f b
  rw [h1, h2, h3, zero_add]

theorem comapInl_apply (μ : (σ ⊕ₗ τ) →₀ ℕ) (a : σ) : comapInl μ a = μ (Sum.inlₗ a) :=
  Finsupp.comapDomain_apply _ _ _ _

theorem comapInr_apply (μ : (σ ⊕ₗ τ) →₀ ℕ) (b : τ) : comapInr μ b = μ (Sum.inrₗ b) :=
  Finsupp.comapDomain_apply _ _ _ _

theorem comapInl_pairExp (e : σ →₀ ℕ) (f : τ →₀ ℕ) : comapInl (pairExp e f) = e := by
  ext a
  rw [comapInl_apply, pairExp_apply_inl]

theorem comapInr_pairExp (e : σ →₀ ℕ) (f : τ →₀ ℕ) : comapInr (pairExp e f) = f := by
  ext b
  rw [comapInr_apply, pairExp_apply_inr]

theorem pairExp_comap (μ : (σ ⊕ₗ τ) →₀ ℕ) : pairExp (comapInl μ) (comapInr μ) = μ := by
  ext i
  have hi : i = toLex (ofLex i) := (toLex_ofLex i).symm
  rcases hx : ofLex i with a | b
  · have hia : i = Sum.inlₗ a := by rw [hi, hx]
    simp only [hia, pairExp_apply_inl, comapInl_apply]
  · have hib : i = Sum.inrₗ b := by rw [hi, hx]
    simp only [hib, pairExp_apply_inr, comapInr_apply]

theorem tdeg_eq_degree (s : σ →₀ ℕ) : tdeg s = Finsupp.degree s := by
  rw [tdeg, Finsupp.degree_eq_sum]

theorem pairExp_tdeg (e : σ →₀ ℕ) (f : τ →₀ ℕ) :
    tdeg (pairExp e f) = tdeg e + tdeg f := by
  rw [tdeg_eq_degree, pairExp, map_add, Finsupp.degree_mapDomain,
    Finsupp.degree_mapDomain, ← tdeg_eq_degree, ← tdeg_eq_degree]

theorem pairExp_tdeg_le (e e₁ : σ →₀ ℕ) (f f₁ : τ →₀ ℕ)
    (h₁ : tdeg e ≤ tdeg e₁) (h₂ : tdeg f ≤ tdeg f₁) :
    tdeg (pairExp e f) ≤ tdeg (pairExp e₁ f₁) := by
  rw [pairExp_tdeg, pairExp_tdeg]; omega

/-! ## The order compatibility -/

theorem lex_pairExp_lt_iff (e e₁ : σ →₀ ℕ) (f f₁ : τ →₀ ℕ) :
    toLex (pairExp e f) < toLex (pairExp e₁ f₁) ↔
      toLex e < toLex e₁ ∨ (e = e₁ ∧ toLex f < toLex f₁) := by
  have h := Commons.Data.Finsupp.lex_mapDomain_lexSum_lt_iff (σ := σ) (τ := τ) e e₁ f f₁
  simpa only [pairExp] using h

theorem dk_pairExp_lt_iff (e e₁ : σ →₀ ℕ) (f f₁ : τ →₀ ℕ) :
    dk (pairExp e f) < dk (pairExp e₁ f₁) ↔
      tdeg e + tdeg f < tdeg e₁ + tdeg f₁ ∨
        (tdeg e + tdeg f = tdeg e₁ + tdeg f₁ ∧
          (toLex e < toLex e₁ ∨ (e = e₁ ∧ toLex f < toLex f₁))) := by
  rw [dk, dk, Prod.Lex.toLex_lt_toLex, pairExp_tdeg, pairExp_tdeg, lex_pairExp_lt_iff]

theorem dk_pairExp_le (e e₁ : σ →₀ ℕ) (f f₁ : τ →₀ ℕ) (h₁ : dk e ≤ dk e₁)
    (h₂ : dk f ≤ dk f₁) : dk (pairExp e f) ≤ dk (pairExp e₁ f₁) := by
  rw [dk_le_iff, pairExp_tdeg, pairExp_tdeg]
  have h1' := (dk_le_iff e e₁).mp h₁
  have h2' := (dk_le_iff f f₁).mp h₂
  rcases h1' with hh1 | ⟨hh1, hh1'⟩
  · left; rcases h2' with hh2 | ⟨hh2, -⟩ <;> omega
  · rcases h2' with hh2 | ⟨hh2, hh2'⟩
    · left; omega
    · right
      refine ⟨by omega, ?_⟩
      by_contra hcon
      push Not at hcon
      rw [lex_pairExp_lt_iff] at hcon
      rcases hcon with h | ⟨he, hf⟩
      · exact absurd h (not_lt.mpr hh1')
      · exact absurd hf (not_lt.mpr hh2')

theorem dk_pairExp_lt_left (e e₁ : σ →₀ ℕ) (f : τ →₀ ℕ) (h : dk e < dk e₁) :
    dk (pairExp e f) < dk (pairExp e₁ f) := by
  rw [dk_pairExp_lt_iff]
  have h' := (dk_le_iff e e₁).mp (le_of_lt h)
  rcases h' with h1 | ⟨h1, h2⟩
  · left; omega
  · right
    refine ⟨by omega, ?_⟩
    rcases lt_or_eq_of_le h2 with h3 | h3
    · exact Or.inl h3
    · exact absurd h (by rw [toLex.injective h3]; exact lt_irrefl _)

theorem dk_pairExp_lt_right (e : σ →₀ ℕ) (f f₁ : τ →₀ ℕ) (h : dk f < dk f₁) :
    dk (pairExp e f) < dk (pairExp e f₁) := by
  rw [dk_pairExp_lt_iff]
  have h' := (dk_le_iff f f₁).mp (le_of_lt h)
  rcases h' with h1 | ⟨h1, h2⟩
  · left; omega
  · right
    refine ⟨by omega, ?_⟩
    rcases lt_or_eq_of_le h2 with h3 | h3
    · exact Or.inr ⟨rfl, h3⟩
    · exact absurd h (by rw [toLex.injective h3]; exact lt_irrefl _)


/-! ## The two-variable product space and the Cartesian corollary -/

noncomputable def renameInl : MvPowerSeries σ ℝ →ₐ[ℝ] MvPowerSeries (σ ⊕ₗ τ) ℝ :=
  MvPowerSeries.rename (⇑(inlEmb (σ := σ) (τ := τ)))

noncomputable def renameInr : MvPowerSeries τ ℝ →ₐ[ℝ] MvPowerSeries (σ ⊕ₗ τ) ℝ :=
  MvPowerSeries.rename (⇑(inrEmb (σ := σ) (τ := τ)))

theorem coeff_prod (u : MvPowerSeries σ ℝ) (v : MvPowerSeries τ ℝ) (μ : (σ ⊕ₗ τ) →₀ ℕ) :
    (MvPowerSeries.coeff μ) (renameInl u * renameInr v) =
      (MvPowerSeries.coeff (comapInl μ)) u * (MvPowerSeries.coeff (comapInr μ)) v := by
  set P₁ := Finsupp.mapDomain (⇑(inlEmb (σ := σ) (τ := τ))) (comapInl μ) with hP₁
  set P₂ := Finsupp.mapDomain (⇑(inrEmb (σ := σ) (τ := τ))) (comapInr μ) with hP₂
  rw [MvPowerSeries.coeff_mul]
  rw [Finset.sum_eq_single (P₁, P₂)]
  · rw [hP₁, hP₂]
    congr 1
    · have h := MvPowerSeries.coeff_embDomain_rename (inlEmb (σ := σ) (τ := τ)) u (comapInl μ)
      rw [Finsupp.embDomain_eq_mapDomain] at h
      exact h
    · have h := MvPowerSeries.coeff_embDomain_rename (inrEmb (σ := σ) (τ := τ)) v (comapInr μ)
      rw [Finsupp.embDomain_eq_mapDomain] at h
      exact h
  · rintro ⟨p₁, p₂⟩ hp hne
    by_cases h1 : p₁ ∈ Set.range (Finsupp.mapDomain (⇑(inlEmb (σ := σ) (τ := τ))))
    · by_cases h2 : p₂ ∈ Set.range (Finsupp.mapDomain (⇑(inrEmb (σ := σ) (τ := τ))))
      · exfalso
        obtain ⟨e', he'⟩ := h1
        obtain ⟨f', hf'⟩ := h2
        have hpμ : p₁ + p₂ = μ := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        have heq1 : comapInl μ = e' := by
          rw [← hpμ, ← he', ← hf']
          exact comapInl_pairExp e' f'
        have heq2 : comapInr μ = f' := by
          rw [← hpμ, ← he', ← hf']
          exact comapInr_pairExp e' f'
        exact hne (by rw [hP₁, hP₂, heq1, heq2, ← he', ← hf'])
      · rw [renameInr, MvPowerSeries.coeff_rename_eq_zero (⇑(inrEmb (σ := σ) (τ := τ))) v h2,
          mul_zero]
    · rw [renameInl, MvPowerSeries.coeff_rename_eq_zero (⇑(inlEmb (σ := σ) (τ := τ))) u h1,
        zero_mul]
  · intro hnotin
    refine absurd ?_ hnotin
    rw [Finset.HasAntidiagonal.mem_antidiagonal, hP₁, hP₂]
    exact pairExp_comap μ

theorem coeff_finsuppSum_gen {ι : Type*} (c : ι →₀ ℝ) (g : ι → ℝ → MvPowerSeries σ ℝ)
    (e : σ →₀ ℕ) :
    (MvPowerSeries.coeff e) (c.sum g) =
      c.sum (fun p r => (MvPowerSeries.coeff e) (g p r)) := by
  rw [Finsupp.sum, Finsupp.sum, map_sum]

theorem coeff_sum_prod {V : Submodule ℝ (MvPowerSeries σ ℝ)}
    {W : Submodule ℝ (MvPowerSeries τ ℝ)} (c : (↥V × ↥W) →₀ ℝ) (μ : (σ ⊕ₗ τ) →₀ ℕ) :
    (MvPowerSeries.coeff μ)
        (c.sum fun p r => r • (renameInl (p.1 : MvPowerSeries σ ℝ) *
          renameInr (p.2 : MvPowerSeries τ ℝ))) =
      c.sum fun p r => r * ((MvPowerSeries.coeff (comapInl μ)) (p.1 : MvPowerSeries σ ℝ) *
        (MvPowerSeries.coeff (comapInr μ)) (p.2 : MvPowerSeries τ ℝ)) := by
  rw [coeff_finsuppSum_gen, Finsupp.sum, Finsupp.sum]
  exact Finset.sum_congr rfl fun p _ => by rw [map_smul, smul_eq_mul, coeff_prod]

noncomputable def genVW (V : Submodule ℝ (MvPowerSeries σ ℝ))
    (W : Submodule ℝ (MvPowerSeries τ ℝ)) : ↥V × ↥W → MvPowerSeries (σ ⊕ₗ τ) ℝ :=
  fun p => renameInl (p.1 : MvPowerSeries σ ℝ) * renameInr (p.2 : MvPowerSeries τ ℝ)

noncomputable def prodSpace (V : Submodule ℝ (MvPowerSeries σ ℝ))
    (W : Submodule ℝ (MvPowerSeries τ ℝ)) : Submodule ℝ (MvPowerSeries (σ ⊕ₗ τ) ℝ) :=
  Submodule.span ℝ (Set.range (genVW V W))

theorem mem_prodSpace_iff {V : Submodule ℝ (MvPowerSeries σ ℝ)}
    {W : Submodule ℝ (MvPowerSeries τ ℝ)} {G : MvPowerSeries (σ ⊕ₗ τ) ℝ} :
    G ∈ prodSpace V W ↔ ∃ c : (↥V × ↥W) →₀ ℝ,
      G = c.sum (fun p r => r • genVW V W p) := by
  rw [prodSpace, ← Finsupp.range_linearCombination (R := ℝ) (v := genVW V W)]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩

theorem coeff_sum_gen {V : Submodule ℝ (MvPowerSeries σ ℝ)}
    {W : Submodule ℝ (MvPowerSeries τ ℝ)} (c : (↥V × ↥W) →₀ ℝ) (μ : (σ ⊕ₗ τ) →₀ ℕ) :
    (MvPowerSeries.coeff μ) (c.sum fun p r => r • genVW V W p) =
      c.sum fun p r => r * ((MvPowerSeries.coeff (comapInl μ)) (p.1 : MvPowerSeries σ ℝ) *
        (MvPowerSeries.coeff (comapInr μ)) (p.2 : MvPowerSeries τ ℝ)) := by
  rw [coeff_finsuppSum_gen, Finsupp.sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, smul_eq_mul, genVW, coeff_prod]

/-! ### The inclusion `𝒱(V)·𝒱(W) ⊆ 𝒱(V ⊗ W)` -/

set_option maxHeartbeats 800000 in
theorem jumpSet_subset_prodSpace {V : Submodule ℝ (MvPowerSeries σ ℝ)}
    {W : Submodule ℝ (MvPowerSeries τ ℝ)} {e : σ →₀ ℕ} {f : τ →₀ ℕ}
    (he : dk e ∈ jumpSet V) (hf : dk f ∈ jumpSet W) :
    dk (pairExp e f) ∈ jumpSet (prodSpace V W) := by
  obtain ⟨u, hu, huV, hule⟩ := he
  obtain ⟨v, hv, hvV, hvle⟩ := hf
  set G := renameInl u * renameInr v with hGdef
  have hcoeff : (MvPowerSeries.coeff (pairExp e f)) G ≠ 0 := by
    rw [hGdef, coeff_prod, comapInl_pairExp, comapInr_pairExp]
    have he' : e = udk (leadExp u hu) := by rw [hule, udk_dk]
    have hf' : f = udk (leadExp v hv) := by rw [hvle, udk_dk]
    rw [he', hf']
    exact mul_ne_zero (coeff_leadExp_ne_zero u hu) (coeff_leadExp_ne_zero v hv)
  have hGne : G ≠ 0 := fun h => hcoeff (by rw [h]; simp)
  have hmin : ∀ ν : (σ ⊕ₗ τ) →₀ ℕ, (MvPowerSeries.coeff ν) G ≠ 0 →
      dk (pairExp e f) ≤ dk ν := by
    intro ν hν
    rw [hGdef, coeff_prod] at hν
    have h1 : dk e ≤ dk (comapInl ν) := by
      have h := leadExp_le_of_coeff_ne_zero u hu (fun h0 => hν (by rw [h0, zero_mul]))
      rwa [hule] at h
    have h2 : dk f ≤ dk (comapInr ν) := by
      have h := leadExp_le_of_coeff_ne_zero v hv (fun h0 => hν (by rw [h0, mul_zero]))
      rwa [hvle] at h
    have h3 := dk_pairExp_le e (comapInl ν) f (comapInr ν) h1 h2
    rwa [pairExp_comap] at h3
  have hminDeg : minDeg G hGne = tdeg (pairExp e f) := by
    refine le_antisymm (minDeg_le G hGne hcoeff) ?_
    obtain ⟨s, hs, hs'⟩ := minDeg_spec G hGne
    have h := (dk_le_iff (pairExp e f) s).mp (hmin s hs')
    have h2 : tdeg (pairExp e f) ≤ tdeg s := by rcases h with h | ⟨h, -⟩ <;> omega
    rw [← hs]
    exact h2
  refine ⟨G, hGne, ?_, ?_⟩
  · rw [hGdef]
    exact Submodule.subset_span
      (Set.mem_range_self (f := genVW V W) (i := (⟨u, huV⟩, ⟨v, hvV⟩)))
  · refine le_antisymm (leadExp_le G hGne hcoeff hminDeg.symm) ?_
    have h := hmin (udk (leadExp G hGne)) (coeff_leadExp_ne_zero G hGne)
    rwa [dk_udk_leadExp G hGne] at h

/-! ### The inclusion `𝒱(V ⊗ W) ⊆ 𝒱(V)·𝒱(W)` -/

/-! ### Coefficient extraction -/

theorem coeff_extract_sigma {V : Submodule ℝ (MvPowerSeries σ ℝ)}
    {W : Submodule ℝ (MvPowerSeries τ ℝ)} (c : (↥V × ↥W) →₀ ℝ) (μ : (σ ⊕ₗ τ) →₀ ℕ) :
    (MvPowerSeries.coeff (comapInl μ))
        (c.sum fun p r => (r * (MvPowerSeries.coeff (comapInr μ) (p.2 : MvPowerSeries τ ℝ))) •
          (p.1 : MvPowerSeries σ ℝ)) =
      (MvPowerSeries.coeff μ) (c.sum fun p r => r • genVW V W p) := by
  rw [coeff_sum_gen, coeff_finsuppSum_gen, Finsupp.sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, smul_eq_mul]
  ring

theorem coeff_extract_tau {V : Submodule ℝ (MvPowerSeries σ ℝ)}
    {W : Submodule ℝ (MvPowerSeries τ ℝ)} (c : (↥V × ↥W) →₀ ℝ) (μ : (σ ⊕ₗ τ) →₀ ℕ) :
    (MvPowerSeries.coeff (comapInr μ))
        (c.sum fun p r => (r * (MvPowerSeries.coeff (comapInl μ) (p.1 : MvPowerSeries σ ℝ))) •
          (p.2 : MvPowerSeries τ ℝ)) =
      (MvPowerSeries.coeff μ) (c.sum fun p r => r • genVW V W p) := by
  rw [coeff_sum_gen, coeff_finsuppSum_gen, Finsupp.sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, smul_eq_mul]
  ring

theorem coeff_extract_right {V : Submodule ℝ (MvPowerSeries σ ℝ)}
    {W : Submodule ℝ (MvPowerSeries τ ℝ)} (c : (↥V × ↥W) →₀ ℝ) (e : σ →₀ ℕ)
    (ν : τ →₀ ℕ) :
    (MvPowerSeries.coeff (pairExp e ν)) (c.sum fun p r => r • genVW V W p) =
      (MvPowerSeries.coeff e)
        (c.sum fun p r => (r * (MvPowerSeries.coeff ν (p.2 : MvPowerSeries τ ℝ))) •
          (p.1 : MvPowerSeries σ ℝ)) := by
  rw [coeff_sum_gen, coeff_finsuppSum_gen, Finsupp.sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, smul_eq_mul, comapInl_pairExp, comapInr_pairExp]
  ring

theorem coeff_extract_left {V : Submodule ℝ (MvPowerSeries σ ℝ)}
    {W : Submodule ℝ (MvPowerSeries τ ℝ)} (c : (↥V × ↥W) →₀ ℝ) (ν : σ →₀ ℕ)
    (f : τ →₀ ℕ) :
    (MvPowerSeries.coeff (pairExp ν f)) (c.sum fun p r => r • genVW V W p) =
      (MvPowerSeries.coeff f)
        (c.sum fun p r => (r * (MvPowerSeries.coeff ν (p.1 : MvPowerSeries σ ℝ))) •
          (p.2 : MvPowerSeries τ ℝ)) := by
  rw [coeff_sum_gen, coeff_finsuppSum_gen, Finsupp.sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, smul_eq_mul, comapInl_pairExp, comapInr_pairExp]
  ring

/-! ### The inclusion `𝒱(V ⊗ W) ⊆ 𝒱(V)·𝒱(W)` -/

set_option maxHeartbeats 800000 in
theorem exists_pair_leadExp_sum {V : Submodule ℝ (MvPowerSeries σ ℝ)}
    {W : Submodule ℝ (MvPowerSeries τ ℝ)} (c : (↥V × ↥W) →₀ ℝ)
    (hF : (c.sum fun p r => r • genVW V W p) ≠ 0) :
    ∃ e : σ →₀ ℕ, ∃ f : τ →₀ ℕ, dk e ∈ jumpSet V ∧ dk f ∈ jumpSet W ∧
      leadExp (c.sum fun p r => r • genVW V W p) hF = dk (pairExp e f) := by
  classical
  set μ := udk (leadExp (c.sum fun p r => r • genVW V W p) hF) with hμdef
  have hlead : leadExp (c.sum fun p r => r • genVW V W p) hF = dk μ := by
    rw [hμdef]
    exact (dk_udk_leadExp _ hF).symm
  have hμ : (MvPowerSeries.coeff μ) (c.sum fun p r => r • genVW V W p) ≠ 0 :=
    coeff_leadExp_ne_zero _ hF
  set H : MvPowerSeries σ ℝ := c.sum (fun p r =>
    (r * (MvPowerSeries.coeff (comapInr μ) (p.2 : MvPowerSeries τ ℝ))) •
      (p.1 : MvPowerSeries σ ℝ)) with hHdef
  set H' : MvPowerSeries τ ℝ := c.sum (fun p r =>
    (r * (MvPowerSeries.coeff (comapInl μ) (p.1 : MvPowerSeries σ ℝ))) •
      (p.2 : MvPowerSeries τ ℝ)) with hH'def
  have hcoeffH : (MvPowerSeries.coeff (comapInl μ)) H =
      (MvPowerSeries.coeff μ) (c.sum fun p r => r • genVW V W p) := coeff_extract_sigma c μ
  have hcoeffH' : (MvPowerSeries.coeff (comapInr μ)) H' =
      (MvPowerSeries.coeff μ) (c.sum fun p r => r • genVW V W p) := coeff_extract_tau c μ
  have hHmem : H ∈ V := by
    rw [hHdef, Finsupp.sum]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ p.1.2
  have hH'mem : H' ∈ W := by
    rw [hH'def, Finsupp.sum]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ p.2.2
  have hHne : H ≠ 0 := fun h => hμ (by rw [← hcoeffH, h]; simp)
  have hH'ne : H' ≠ 0 := fun h => hμ (by rw [← hcoeffH', h]; simp)
  have he_le : dk (udk (leadExp H hHne)) ≤ dk (comapInl μ) := by
    have h := leadExp_le_of_coeff_ne_zero H hHne (by rw [hcoeffH]; exact hμ)
    rwa [← dk_udk_leadExp H hHne] at h
  have hf_le : dk (udk (leadExp H' hH'ne)) ≤ dk (comapInr μ) := by
    have h := leadExp_le_of_coeff_ne_zero H' hH'ne (by rw [hcoeffH']; exact hμ)
    rwa [← dk_udk_leadExp H' hH'ne] at h
  have he_eq : dk (udk (leadExp H hHne)) = dk (comapInl μ) := by
    rcases lt_or_eq_of_le he_le with hlt | heq
    · exfalso
      have hstrict := dk_pairExp_lt_left (udk (leadExp H hHne)) (comapInl μ) (comapInr μ) hlt
      rw [pairExp_comap] at hstrict
      have h2 : (MvPowerSeries.coeff (pairExp (udk (leadExp H hHne)) (comapInr μ)))
          (c.sum fun p r => r • genVW V W p) = (MvPowerSeries.coeff (udk (leadExp H hHne))) H :=
        coeff_extract_right c _ _
      have hmin : dk μ ≤ dk (pairExp (udk (leadExp H hHne)) (comapInr μ)) := by
        have h := leadExp_le_of_coeff_ne_zero _ hF
          (by rw [h2]; exact coeff_leadExp_ne_zero H hHne)
        rwa [hlead] at h
      exact absurd hstrict (not_lt.mpr hmin)
    · exact heq
  have hf_eq : dk (udk (leadExp H' hH'ne)) = dk (comapInr μ) := by
    rcases lt_or_eq_of_le hf_le with hlt | heq
    · exfalso
      have hstrict := dk_pairExp_lt_right (comapInl μ) (udk (leadExp H' hH'ne)) (comapInr μ) hlt
      rw [pairExp_comap] at hstrict
      have h2 : (MvPowerSeries.coeff (pairExp (comapInl μ) (udk (leadExp H' hH'ne))))
          (c.sum fun p r => r • genVW V W p) = (MvPowerSeries.coeff (udk (leadExp H' hH'ne))) H' :=
        coeff_extract_left c _ _
      have hmin : dk μ ≤ dk (pairExp (comapInl μ) (udk (leadExp H' hH'ne))) := by
        have h := leadExp_le_of_coeff_ne_zero _ hF
          (by rw [h2]; exact coeff_leadExp_ne_zero H' hH'ne)
        rwa [hlead] at h
      exact absurd hstrict (not_lt.mpr hmin)
    · exact heq
  have he_eq' : udk (leadExp H hHne) = comapInl μ := (dk_injective (σ := σ)) he_eq
  have hf_eq' : udk (leadExp H' hH'ne) = comapInr μ := (dk_injective (σ := τ)) hf_eq
  refine ⟨udk (leadExp H hHne), udk (leadExp H' hH'ne),
    ⟨H, hHne, hHmem, (dk_udk_leadExp H hHne).symm⟩,
    ⟨H', hH'ne, hH'mem, (dk_udk_leadExp H' hH'ne).symm⟩, ?_⟩
  rw [hlead, he_eq', hf_eq', pairExp_comap]

/-! ### The Cartesian product theorem -/

theorem jumpSet_prodSpace (V : Submodule ℝ (MvPowerSeries σ ℝ))
    (W : Submodule ℝ (MvPowerSeries τ ℝ)) :
    jumpSet (prodSpace V W) =
      {key | ∃ e : σ →₀ ℕ, ∃ f : τ →₀ ℕ, dk e ∈ jumpSet V ∧ dk f ∈ jumpSet W ∧
        key = dk (pairExp e f)} := by
  ext key
  constructor
  · rintro ⟨G, hG, hGmem, hlead⟩
    obtain ⟨c, hc⟩ := mem_prodSpace_iff.mp hGmem
    subst hc
    obtain ⟨e, f, he, hf, hle⟩ := exists_pair_leadExp_sum c hG
    exact ⟨e, f, he, hf, by rw [← hlead]; exact hle⟩
  · rintro ⟨e, f, he, hf, rfl⟩
    exact jumpSet_subset_prodSpace he hf

end Submission.CDT.MvVanishing
