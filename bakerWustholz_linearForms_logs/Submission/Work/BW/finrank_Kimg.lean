import Mathlib
import Submission.Work.BW.Kimg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The degree of the Kummer extension over the image of `K`

`L = EL φ ρ = ℚ(φ(K), ρ₁,…,ρ_r)` is generated over the copy `Kimg φ ρ = φ(K)` of `K` by the
square roots `rhoE φ ρ j` of `φ(η j)`, and `rhoE φ ρ j ^ 2 = inclE φ ρ (η j)`.

We prove `[L : Kimg φ ρ] = 2 ^ r` in two steps.

* The `2 ^ r` products `∏ i, (rhoE φ ρ i) ^ (ε i : ℕ)` (`ε : Fin r → Fin 2`) are linearly
  independent over `Kimg φ ρ`: a dependence, transported to `ℂ`, contradicts `kummer_indep`.
* Their `Kimg φ ρ`-span `monoSpan φ ρ` is all of `L`: it is a `Kimg φ ρ`-subalgebra of the field
  `L` (closed under products by `mono_mul`) which is closed under inverses, because the minimal
  polynomial over `Kimg φ ρ` of a nonzero `y ∈ monoSpan φ ρ` has nonzero constant coefficient
  `c₀`, so that the identity `X * q + C c₀ = minpoly` evaluated at `y` exhibits `y⁻¹` as
  `-(c₀⁻¹ • q(y)) ∈ monoSpan φ ρ`.  So the image of `monoSpan φ ρ` in `ℂ` is a subfield of `ℂ`
  containing `ℚ`, the image of `φ(K)` and the `ρ j`, and therefore contains `EL φ ρ` by the
  inductive description of the `ℚ`-adjoin.
-/

namespace Work.BW

open Complex
open Polynomial
open scoped Pointwise

set_option synthInstance.maxHeartbeats 400000

variable {K : Type*} [Field K] [NumberField K] {r : ℕ}

/-- The `2 ^ r` monomials `∏ i, ρᵢ ^ εᵢ` in `L = EL φ ρ` (`ε : Fin r → Fin 2`). -/
private noncomputable def mono (φ : K →+* ℂ) (ρ : Fin r → ℂ) (ε : Fin r → Fin 2) : EL φ ρ :=
  ∏ i, (rhoE φ ρ i) ^ (ε i : ℕ)

/-- The `Kimg φ ρ`-span of the `2 ^ r` monomials; it is a `Kimg φ ρ`-subalgebra of `L`. -/
noncomputable def monoSpan (φ : K →+* ℂ) (ρ : Fin r → ℂ) : Submodule ↥(Kimg φ ρ) (EL φ ρ) :=
  Submodule.span ↥(Kimg φ ρ) (Set.range (mono φ ρ))

/-- The generators of `EL φ ρ` over `ℚ`, as a subset of `ℂ`. -/
noncomputable def ELgens (φ : K →+* ℂ) (ρ : Fin r → ℂ) : Set ℂ :=
  Set.range (fun i => φ (kbasis K i)) ∪ Set.range ρ

/-- The image in `ℂ` of `Kimg φ ρ` together with the `ρ j`. -/
noncomputable def KimgGens (φ : K →+* ℂ) (ρ : Fin r → ℂ) : Set ℂ :=
  Set.range (fun c : ↥(Kimg φ ρ) => ((c : EL φ ρ) : ℂ)) ∪ Set.range ρ

variable {φ : K →+* ℂ} {ρ : Fin r → ℂ}

theorem mono_zero : mono φ ρ (0 : Fin r → Fin 2) = 1 := by
  simp [mono]

theorem mono_single (j : Fin r) : mono φ ρ (Pi.single j 1) = rhoE φ ρ j := by
  have h := Finset.prod_eq_single_of_mem (s := Finset.univ)
    (f := fun i : Fin r => (rhoE φ ρ i) ^ ((Pi.single j (1 : Fin 2) : Fin r → Fin 2) i : ℕ))
    j (Finset.mem_univ j) (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp)
  simpa [mono] using h

private lemma pow_mod (x : EL φ ρ) (m : ℕ) : x ^ m = (x ^ 2) ^ (m / 2) * x ^ (m % 2) := by
  conv_lhs => rw [← Nat.div_add_mod m 2]
  rw [pow_add, pow_mul]

private lemma div2_mul (a b : Fin 2) : ((a : ℕ) + (b : ℕ)) / 2 = (a : ℕ) * (b : ℕ) := by
  fin_cases a <;> fin_cases b <;> decide

/-- Multiplication of monomials: the product of two monomials is an element of `Kimg φ ρ` times a
monomial. -/
theorem mono_mul {η : Fin r → K} (hρ : ∀ j, ρ j ^ 2 = φ (η j)) (ε δ : Fin r → Fin 2) :
    mono φ ρ ε * mono φ ρ δ =
      inclE φ ρ (∏ i, η i ^ ((ε i : ℕ) * (δ i : ℕ))) * mono φ ρ (ε + δ) := by
  simp only [mono]
  rw [map_prod (inclE φ ρ), ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Pi.add_apply, Fin.val_add]
  rw [← pow_add]
  rw [show (rhoE φ ρ i) ^ ((ε i : ℕ) + (δ i : ℕ)) =
        ((rhoE φ ρ i) ^ 2) ^ (((ε i : ℕ) + (δ i : ℕ)) / 2) *
          (rhoE φ ρ i) ^ (((ε i : ℕ) + (δ i : ℕ)) % 2)
      from pow_mod (rhoE φ ρ i) ((ε i : ℕ) + (δ i : ℕ)), rhoE_sq hρ i, ← map_pow,
    div2_mul (ε i) (δ i)]

theorem one_mem_monoSpan : (1 : EL φ ρ) ∈ monoSpan φ ρ := by
  rw [← mono_zero (φ := φ) (ρ := ρ)]
  exact Submodule.subset_span (Set.mem_range_self 0)

theorem coe_mem_monoSpan (c : ↥(Kimg φ ρ)) : (c : EL φ ρ) ∈ monoSpan φ ρ := by
  have h : c • (1 : EL φ ρ) ∈ monoSpan φ ρ := Submodule.smul_mem _ c one_mem_monoSpan
  simpa [Algebra.smul_def] using h

/-- `monoSpan φ ρ` is closed under multiplication. -/
theorem mul_mem_monoSpan {η : Fin r → K} (hρ : ∀ j, ρ j ^ 2 = φ (η j)) {x y : EL φ ρ}
    (hx : x ∈ monoSpan φ ρ) (hy : y ∈ monoSpan φ ρ) : x * y ∈ monoSpan φ ρ := by
  have hmul : (Set.range (mono φ ρ)) * (Set.range (mono φ ρ)) ⊆
      (monoSpan φ ρ : Set (EL φ ρ)) := by
    rintro z ⟨a, ⟨ε, rfl⟩, b, ⟨δ, rfl⟩, rfl⟩
    change mono φ ρ ε * mono φ ρ δ ∈ (monoSpan φ ρ : Set (EL φ ρ))
    rw [mono_mul hρ ε δ]
    exact Submodule.smul_mem _
      (⟨inclE φ ρ (∏ i, η i ^ ((ε i : ℕ) * (δ i : ℕ))), inclE_mem_Kimg _⟩ : ↥(Kimg φ ρ))
      (Submodule.subset_span (Set.mem_range_self (ε + δ)))
  have hSS : monoSpan φ ρ * monoSpan φ ρ ≤ monoSpan φ ρ := by
    simp only [monoSpan]
    rw [Submodule.span_mul_span]
    exact Submodule.span_le.mpr hmul
  exact hSS (Submodule.mul_mem_mul hx hy)

/-- `monoSpan φ ρ` is closed under inverses: if `y ∈ monoSpan φ ρ` is nonzero, its minimal
polynomial over `Kimg φ ρ` has nonzero constant coefficient `c₀`, and the relation
`X * q + C c₀ = minpoly` evaluated at `y` gives `y * (c₀⁻¹ • q(y)) = -1`, so that
`y⁻¹ = -(c₀⁻¹ • q(y)) ∈ monoSpan φ ρ`. -/
theorem inv_mem_monoSpan {η : Fin r → K} (hρ : ∀ j, ρ j ^ 2 = φ (η j)) [NumberField (EL φ ρ)]
    {y : EL φ ρ} (hy : y ∈ monoSpan φ ρ) : y⁻¹ ∈ monoSpan φ ρ := by
  by_cases hy0 : y = 0
  · rw [hy0, inv_zero]
    exact Submodule.zero_mem _
  · haveI hfin : Module.Finite ↥(Kimg φ ρ) (EL φ ρ) :=
      Module.Finite.of_restrictScalars_finite ℚ _ _
    have hpow : ∀ n : ℕ, y ^ n ∈ monoSpan φ ρ := by
      intro n
      induction n with
      | zero => simpa using one_mem_monoSpan
      | succ n ih => rw [pow_succ]; exact mul_mem_monoSpan hρ ih hy
    have haeval : ∀ q : Polynomial ↥(Kimg φ ρ), aeval y q ∈ monoSpan φ ρ := by
      intro q
      rw [Polynomial.aeval_eq_sum_range]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hpow i)
    set p := minpoly ↥(Kimg φ ρ) y with hp
    have hp0 : p.coeff 0 ≠ 0 := by
      rw [hp]
      exact minpoly.coeff_zero_ne_zero (IsIntegral.of_finite ↥(Kimg φ ρ) y) hy0
    have hrel : y * aeval y (Polynomial.divX p) = -(algebraMap ↥(Kimg φ ρ) (EL φ ρ) (p.coeff 0)) := by
      have h := minpoly.aeval (A := ↥(Kimg φ ρ)) y
      rw [← hp, ← Polynomial.X_mul_divX_add p, map_add, Polynomial.aeval_mul,
        Polynomial.aeval_X, Polynomial.aeval_C] at h
      exact add_eq_zero_iff_eq_neg.mp h
    have hw : aeval y (Polynomial.divX p) ∈ monoSpan φ ρ := haeval _
    have hmem : -((p.coeff 0)⁻¹ • aeval y (Polynomial.divX p)) ∈ monoSpan φ ρ :=
      Submodule.neg_mem _ (Submodule.smul_mem _ _ hw)
    have hmul : y * (-((p.coeff 0)⁻¹ • aeval y (Polynomial.divX p))) = 1 := by
      have h1 : y * ((p.coeff 0)⁻¹ • aeval y (Polynomial.divX p)) =
          (p.coeff 0)⁻¹ • (y * aeval y (Polynomial.divX p)) := by
        rw [Algebra.smul_def, Algebra.smul_def]
        ring
      rw [mul_neg, h1, hrel, smul_neg, neg_neg, Algebra.smul_def, ← map_mul,
        inv_mul_cancel₀ hp0, map_one]
    have hfin : y⁻¹ = -((p.coeff 0)⁻¹ • aeval y (Polynomial.divX p)) := by
      refine mul_left_cancel₀ hy0 ?_
      rw [mul_inv_cancel₀ hy0, hmul]
    rw [hfin]
    exact hmem

/-- `monoSpan φ ρ` is the whole of `L = EL φ ρ`: it is a finite dimensional `Kimg φ ρ`-subalgebra
of the field `L` closed under inverses, and its image in `ℂ` contains the `ℚ`-generators of `L`. -/
theorem monoSpan_eq_top {η : Fin r → K} (hρ : ∀ j, ρ j ^ 2 = φ (η j)) [NumberField (EL φ ρ)] :
    monoSpan φ ρ = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  have hgens : ELgens φ ρ ⊆ KimgGens φ ρ := by
    intro z hz
    rcases hz with ⟨i, rfl⟩ | hz
    · exact Or.inl ⟨⟨inclE φ ρ (kbasis K i), inclE_mem_Kimg _⟩, rfl⟩
    · exact Or.inr hz
  have hclos := Subfield.closure_mono (Set.union_subset_union (fun _ hz => hz : Set.range (algebraMap ℚ ℂ) ⊆ Set.range (algebraMap ℚ ℂ)) hgens)
  have key : ∀ x ∈ Subfield.closure (Set.range (algebraMap ℚ ℂ) ∪ KimgGens φ ρ),
      ∃ (h : x ∈ EL φ ρ), (⟨x, h⟩ : EL φ ρ) ∈ monoSpan φ ρ := by
    intro x hx
    refine Subfield.closure_induction
      (p := fun z _ => ∃ (h : z ∈ EL φ ρ), (⟨z, h⟩ : EL φ ρ) ∈ monoSpan φ ρ)
      ?_ ?_ ?_ ?_ ?_ ?_ hx
    · -- the generators
      rintro z (⟨q, rfl⟩ | hz)
      · refine ⟨IntermediateField.algebraMap_mem (S := EL φ ρ) q, ?_⟩
        have h2 : algebraMap ℚ (EL φ ρ) q ∈ monoSpan φ ρ := by
          rw [IsScalarTower.algebraMap_apply ℚ ↥(Kimg φ ρ) (EL φ ρ) q]
          exact coe_mem_monoSpan (algebraMap ℚ ↥(Kimg φ ρ) q)
        exact h2
      · rcases hz with ⟨c, rfl⟩ | ⟨j, rfl⟩
        · exact ⟨(c : EL φ ρ).2, coe_mem_monoSpan c⟩
        · refine ⟨(rhoE φ ρ j).2, ?_⟩
          have h : mono φ ρ (Pi.single j 1) ∈ monoSpan φ ρ :=
            Submodule.subset_span (Set.mem_range_self _)
          rw [mono_single (φ := φ) (ρ := ρ) j] at h
          exact h
    · -- `1`
      exact ⟨one_mem (EL φ ρ), one_mem_monoSpan⟩
    · -- addition
      rintro x y _ _ ⟨hx, px⟩ ⟨hy, py⟩
      exact ⟨add_mem hx hy, Submodule.add_mem _ px py⟩
    · -- negation
      rintro x _ ⟨hx, px⟩
      exact ⟨neg_mem hx, Submodule.neg_mem _ px⟩
    · -- inverse
      rintro x _ ⟨hx, px⟩
      exact ⟨inv_mem hx, inv_mem_monoSpan hρ px⟩
    · -- multiplication
      rintro x y _ _ ⟨hx, px⟩ ⟨hy, py⟩
      exact ⟨mul_mem hx hy, mul_mem_monoSpan hρ px py⟩
  have hyS : (y : ℂ) ∈ Subfield.closure (Set.range (algebraMap ℚ ℂ) ∪ ELgens φ ρ) := by
    have h : (y : ℂ) ∈ (IntermediateField.adjoin ℚ (ELgens φ ρ)).toSubfield := y.property
    rwa [IntermediateField.adjoin_toSubfield] at h
  obtain ⟨h, hmem⟩ := key ((y : EL φ ρ) : ℂ) (hclos hyS)
  simpa using hmem

/-- `L = EL φ ρ = ℚ(φ(K), ρ₁,…,ρ_r)` has degree `2^r` over the copy `Kimg φ ρ = φ(K)` of `K`,
because `ρ_j² = φ(η_j)` and the `η_j` satisfy the Kummer condition.

`Kimg φ ρ` and `KimgEquiv : K ≃ₐ[ℚ] Kimg φ ρ` are defined in `Submission/Work/BW/Kimg.lean`
(module `Submission.Work.BW.Kimg`), which you should import.  The `ρ_j` as elements of `L` are
`rhoE φ ρ j`, with `rhoE φ ρ j ^ 2 = inclE φ ρ (η j)` (`Work.BW.rhoE_sq`) and
`((rhoE φ ρ j : EL φ ρ) : ℂ) = ρ j`, `((inclE φ ρ x : EL φ ρ) : ℂ) = φ x` — all in
`Submission/Work/BW/Est17Ext.lean` (module `Submission.Work.BW.Est17Ext`, re-exported by
`Kimg`).

Proof route. (1) `EL φ ρ = ⊤` over `Kimg φ ρ` generated by `rhoE φ ρ`, i.e.
`IntermediateField.adjoin (Kimg φ ρ) (Set.range (rhoE φ ρ)) = ⊤`: both sides contain
`inclE φ ρ (kbasis K i)` (`Work.BW.inclE_mem_Kimg`) and `Set.range ρ`, and `EL φ ρ` is the
`ℚ`-adjoin of exactly those (`Work.BW.kbasis`, `Work.BW.EL`), so `adjoin_le_iff` finishes.
(2) Lower bound `2^r ≤ finrank`: `Work.BW.kummer_indep` gives
`∑ ε, φ (a ε) * ∏ i, ρ i ^ (ε i) = 0 → a = 0`; since `((· : EL φ ρ) : ℂ)` is injective, this is
`Kimg`-linear independence of the `2^r` products `∏ i, (rhoE φ ρ i) ^ (ε i : ℕ)`, `ε : Fin r → Fin 2`
(use `KimgEquiv` to move coefficients to `K`), so `LinearIndependent.fintype_card_le_finrank`
and `Fintype.card (Fin r → Fin 2) = 2 ^ r` finish.
(3) Upper bound `finrank ≤ 2^r`: iterate the tower formula
`Module.finrank_mul_finrank`, adjoining the `rhoE φ ρ j` one at a time; at each step
`rhoE φ ρ j` is a root of the monic quadratic `X ^ 2 - C (inclE φ ρ (η j))` over the smaller
field (so `natDegree (minpoly _ _) ≤ 2` via `minpoly.dvd` and `Polynomial.natDegree_le_of_dvd`,
or directly `minpoly.degree_le_of_ne_zero`), and `IntermediateField.adjoin.finrank` converts the
adjoin degree into that `natDegree`.  Alternatively show that
`Submodule.span (Kimg φ ρ) (Set.range (fun ε : Fin r → Fin 2 => ∏ i, (rhoE φ ρ i) ^ (ε i : ℕ))) = ⊤`
(the same closure arguments as `Work.BW.ksp_mul` / `Work.BW.ksp_inv` in
`Submission/Work/BW/kummer_indep.lean`, with `φ(K)` replaced by `Kimg φ ρ`) and bound
`finrank ≤ Fintype.card (Fin r → Fin 2) = 2^r` by the size of a spanning set. -/
theorem finrank_Kimg {K : Type*} [Field K] [NumberField K] {r : ℕ} {φ : K →+* ℂ}
    {ρ : Fin r → ℂ} {η : Fin r → K} (hη : ∀ j, η j ≠ 0)
    (hρ : ∀ j, ρ j ^ 2 = φ (η j)) (hK : KummerCond η) [NumberField (EL φ ρ)] :
    Module.finrank ↥(Kimg φ ρ) (EL φ ρ) = 2 ^ r := by
  haveI hfin : Module.Finite ↥(Kimg φ ρ) (EL φ ρ) :=
    Module.Finite.of_restrictScalars_finite ℚ _ _
  have htop : monoSpan φ ρ = ⊤ := monoSpan_eq_top hρ
  have hcard : Fintype.card (Fin r → Fin 2) = 2 ^ r := by simp
  have hle : Module.finrank ↥(Kimg φ ρ) (EL φ ρ) ≤ 2 ^ r := by
    rw [← hcard]
    exact finrank_le_of_span_eq_top (R := ↥(Kimg φ ρ)) (M := EL φ ρ) (v := mono φ ρ) htop
  have hge : 2 ^ r ≤ Module.finrank ↥(Kimg φ ρ) (EL φ ρ) := by
    rw [← hcard]
    refine LinearIndependent.fintype_card_le_finrank
      (b := fun ε : Fin r → Fin 2 => ∏ i, (rhoE φ ρ i) ^ (ε i : ℕ)) ?_
    rw [Fintype.linearIndependent_iff]
    intro c hc
    choose a ha using fun ε => mem_Kimg.mp (c ε).2
    have hc1 : ∑ ε, inclE φ ρ (a ε) * (∏ i, (rhoE φ ρ i) ^ (ε i : ℕ)) = 0 := by
      rw [← hc]
      apply Finset.sum_congr rfl
      intro ε _
      rw [Algebra.smul_def, ha ε]
      rfl
    have hc2 : ∑ ε, φ (a ε) * ∏ i, ρ i ^ (ε i : ℕ) = 0 := by
      have h := congrArg (fun z : EL φ ρ => (z : ℂ)) hc1
      simpa using h
    have ha0 : a = 0 := kummer_indep φ η hη hK ρ hρ a hc2
    intro ε
    apply Subtype.ext
    have h : ((c ε : ↥(Kimg φ ρ)) : EL φ ρ) = 0 := by
      rw [← ha ε, congrFun ha0 ε]
      simp
    simpa using h
  exact le_antisymm hle hge

end Work.BW
