import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.T32Aux
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge
import Submission.Work.BG.rem31Orth
import Submission.Work.BG.lemma24
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.s02_lamOrbit_ne
import Submission.Work.BG.s02_bset_finite
import Submission.Work.BG.s02_sum_irr_eq_finsum_bset
import Submission.Work.BG.sconjLam
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.tConjSum
import Submission.Work.BG.bset_orbit_struct

/-!
# Area BG: Bender–Glauberman 1981, Theorem 3.2 (p. 208)

`Work.GW2.C16.Thm32Prop` states: for `χ ∈ ±Irr(G)`, the support `𝒮(χ)` of `χ` on the
coherent characters has at most three elements.

The proof is the paper's.  Let `S = bset C f χ`, `e_ν = (χ, f ν)` (so `e_ν = ±1` on `S`
and `0` off `S`;  `Work.BG.inner_pmIrr_eq_pm_one`), and let `T = H₀ ∖ U` be the TI-subset
of Bender–Glauberman's Hypothesis 1.2.  By Lemma 2.4 (`Work.BG.lemma24`) and the
TI-counting identity (`OddOrder.GroupTheory.IsTISubset.sum_conjClassSet`),

* `(1/|H₀|)·Σ_{x∈T} |χ(x)|² = |S| − Σ_{ν∈S} (1 + c_ν)/|Λν|`,  where `c_ν = 1` iff
  `ν^s ∈ Λν` and `ν^s ≠ ν`;  the `T`-sum is expanded through the identity on `T` and split
  as `H₀` (orthonormality of `Irr(H₀)`) minus `U` (Remark 3.1, `Work.BG.rem31Orth`);
* `(1/|H₀|)·Σ_{x∈T} |χ(x)|² < 2`, because `T^G` is the disjoint union of `[G : H]`
  conjugates of `T` and `|χ|²` misses part of `G` (`χ(1) ≠ 0`);
* `Σ_{ν∈S} (1 + c_ν)/|Λν| ≤ |S|/2`, since `𝒮(χ)` meets each `Λ`-orbit in at most two
  `s`-conjugate characters, every `Λ`-orbit has at least two elements, and an `s`-stable
  orbit containing a non-`s`-fixed character has at least four.

Hence `|S|/2 < 2`, i.e. `|S| ≤ 3`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-! ## 1. Auxiliary finsets inside `↥H₀` -/

/-- `T = H₀ ∖ U` of Bender–Glauberman's Hypothesis 1.2, as a finset of `↥H₀`. -/
noncomputable def TfinH (C : Sec2Ctx G) [Fintype ↥C.P.H0] : Finset ↥C.P.H0 := by
  classical exact Finset.univ.filter (fun g : ↥C.P.H0 => (g : G) ∉ C.P.U)

/-- `U ⊆ H₀`, as a finset of `↥H₀` (the complement predicate of `TfinH`, so that the
`T`/`U`-splitting of a sum over `↥H₀` is the standard filter splitting). -/
noncomputable def UfinH (C : Sec2Ctx G) [Fintype ↥C.P.H0] : Finset ↥C.P.H0 := by
  classical exact Finset.univ.filter (fun g : ↥C.P.H0 => ¬ (g : G) ∉ C.P.U)

@[simp] theorem mem_TfinH {C : Sec2Ctx G} [Fintype ↥C.P.H0] {g : ↥C.P.H0} :
    g ∈ TfinH C ↔ (g : G) ∉ C.P.U := by
  classical simp [TfinH]

@[simp] theorem mem_UfinH {C : Sec2Ctx G} [Fintype ↥C.P.H0] {g : ↥C.P.H0} :
    g ∈ UfinH C ↔ (g : G) ∈ C.P.U := by
  classical
  by_cases h : (g : G) ∈ C.P.U <;> simp [UfinH, h]

/-- Splitting a sum over `↥H₀` into its `T`-part and its `U`-part. -/
theorem sum_univ_eq_sum_TfinH_add_sum_UfinH (C : Sec2Ctx G) [Fintype ↥C.P.H0]
    (F : ↥C.P.H0 → ℂ) :
    (∑ g : ↥C.P.H0, F g) = ∑ g ∈ TfinH C, F g + ∑ g ∈ UfinH C, F g := by
  classical
  rw [TfinH, UfinH]
  exact (Finset.sum_filter_add_sum_filter_not (Finset.univ)
    (fun g : ↥C.P.H0 => (g : G) ∉ C.P.U) F).symm

/-! ## 2. The `T`-finset of `G` and of `↥H₀` agree -/

/-- `T` as a finset of `G`, transported to `↥H₀`. -/
theorem sum_Tfin_eq_sum_TfinH (C : Sec2Ctx G) [Fintype ↥C.P.H0] {M : Type*}
    [AddCommMonoid M] (F : G → M) :
    ∑ x ∈ Tfin C, F x = ∑ g ∈ TfinH C, F (g : G) := by
  classical
  have himg : Tfin C = (TfinH C).image (fun g : ↥C.P.H0 => (g : G)) := by
    ext x
    constructor
    · intro hx
      rw [mem_Tfin] at hx
      exact Finset.mem_image.mpr ⟨⟨x, hx.1⟩, by rw [mem_TfinH]; exact hx.2, rfl⟩
    · intro hx
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
      rw [mem_Tfin] at ⊢
      exact ⟨g.2, by rwa [mem_TfinH] at hg⟩
  rw [himg, Finset.sum_image]
  intro a _ b _ hab
  exact Subtype.ext hab

/-- The `U`-sum, as a sum over the subgroup `U` of `↥H₀`. -/
theorem sum_UfinH_eq_sum_Uin (C : Sec2Ctx G) [Fintype ↥C.P.H0] [Fintype ↥(Uin C)]
    (F : ↥C.P.H0 → ℂ) :
    ∑ g ∈ UfinH C, F g = ∑ u : ↥(Uin C), F (u : ↥C.P.H0) := by
  classical
  have himg : UfinH C = (Finset.univ : Finset ↥(Uin C)).image
      (fun u : ↥(Uin C) => (u : ↥C.P.H0)) := by
    ext g
    constructor
    · intro hg
      rw [mem_UfinH] at hg
      exact Finset.mem_image.mpr ⟨⟨g, (Subgroup.mem_subgroupOf).mpr hg⟩, Finset.mem_univ _, rfl⟩
    · intro hg
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hg
      rw [mem_UfinH]
      exact (Subgroup.mem_subgroupOf).mp u.2
  rw [himg, Finset.sum_image]
  intro a _ b _ hab
  exact Subtype.ext hab

/-! ## 3. The coefficient `e_ν = (χ, f ν)` and the identity of Lemma 2.4 on `T` -/

/-- `e_ν = (χ, f ν)`: the coefficient of `ν` in the expansion of `χ` on `T`
(Bender–Glauberman 1981, Lemma 2.4). -/
noncomputable def chiCoef (C : Sec2Ctx G) (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ)
    (χ : ClassFunction G ℂ) (ν : ClassFunction ↥C.P.H0 ℂ) : ℂ :=
  ClassFunction.inner χ (f ν)

/-- **BG Lemma 2.4 on `T`**, in the form of a sum over `Irr(H₀)`: for `g ∈ T`,
`χ(g) = Σ_{ν ∈ Irr(H₀)} e_ν · ν(g)`. -/
theorem chi_expand_T (C : Sec2Ctx G) [Fintype ↥C.P.H0] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) (g : ↥C.P.H0) (hg : (g : G) ∉ C.P.U) :
    χ (g : G) = ∑ ν : IrreducibleCharacter ↥C.P.H0,
      chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) * (ν : ClassFunction ↥C.P.H0 ℂ) g := by
  classical
  have h := (lemma24 C f hf χ hχ).2.1 g hg
  rw [h]
  refine (s02_sum_irr_eq_finsum_bset C f χ
    (fun ξ : ClassFunction ↥C.P.H0 ℂ => chiCoef C f χ ξ * ξ g) ?_).symm
  intro ν hν
  have hz : chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) = 0 := by
    by_contra hc
    exact hν ⟨ν.2, hc⟩
  rw [hz, zero_mul]

/-- `e_ν` is real (`0` or `±1`) for every irreducible `ν`. -/
theorem star_chiCoef (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) (ν : IrreducibleCharacter ↥C.P.H0) :
    star (chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ)) =
      chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) := by
  classical
  by_cases h : (ν : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ
  · rcases (bset_orbit_struct C f hf χ hχ).1 _ h |>.2.2 with hh | hh
    · rw [chiCoef, hh]; norm_num
    · rw [chiCoef, hh]; norm_num
  · have hz : chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) = 0 := by
      by_contra hc
      exact h ⟨ν.2, hc⟩
    rw [hz, star_zero]

/-! ## 4. The two orthogonality sums over `H₀` and over `U` -/

/-- Orthonormality of `Irr(H₀)`, in the form of an unscaled sum. -/
theorem sum_univ_mul_star (C : Sec2Ctx G) [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] (ν μ : IrreducibleCharacter ↥C.P.H0) :
    (∑ g : ↥C.P.H0,
        (ν : ClassFunction ↥C.P.H0 ℂ) g * star ((μ : ClassFunction ↥C.P.H0 ℂ) g)) =
      (Nat.card ↥C.P.H0 : ℂ) *
        ClassFunction.inner (ν : ClassFunction ↥C.P.H0 ℂ)
          (μ : ClassFunction ↥C.P.H0 ℂ) := by
  classical
  show ClassFunction.innerSum (ν : ClassFunction ↥C.P.H0 ℂ)
      (μ : ClassFunction ↥C.P.H0 ℂ) = (Nat.card ↥C.P.H0 : ℂ) *
        ClassFunction.inner (ν : ClassFunction ↥C.P.H0 ℂ)
          (μ : ClassFunction ↥C.P.H0 ℂ)
  exact (ClassFunction.card_mul_inner _ _).symm

/-- The `U`-sum is `|U|` times the inner product of the restrictions to `U`
(Remark 3.1, `Work.BG.rem31Orth`). -/
theorem sum_UfinH_mul_star (C : Sec2Ctx G) [Fintype ↥C.P.H0] [Fintype ↥(Uin C)]
    [Invertible (Nat.card ↥(Uin C) : ℂ)] (ν μ : IrreducibleCharacter ↥C.P.H0) :
    (∑ g ∈ UfinH C,
        (ν : ClassFunction ↥C.P.H0 ℂ) g * star ((μ : ClassFunction ↥C.P.H0 ℂ) g)) =
      (Nat.card ↥(Uin C) : ℂ) * ClassFunction.inner
        (ClassFunction.restrict (Uin C) (ν : ClassFunction ↥C.P.H0 ℂ))
        (ClassFunction.restrict (Uin C) (μ : ClassFunction ↥C.P.H0 ℂ)) := by
  classical
  rw [sum_UfinH_eq_sum_Uin C,
    show (Nat.card ↥(Uin C) : ℂ) * ClassFunction.inner
        (ClassFunction.restrict (Uin C) (ν : ClassFunction ↥C.P.H0 ℂ))
        (ClassFunction.restrict (Uin C) (μ : ClassFunction ↥C.P.H0 ℂ))
        = ClassFunction.innerSum
            (ClassFunction.restrict (Uin C) (ν : ClassFunction ↥C.P.H0 ℂ))
            (ClassFunction.restrict (Uin C) (μ : ClassFunction ↥C.P.H0 ℂ))
      from ClassFunction.card_mul_inner _ _]
  exact Finset.sum_congr rfl fun u _ => by simp [ClassFunction.restrict_apply]

/-! ## 5. Expanding the `T`-sum into a double sum over `Irr(H₀)` -/

/-- `Σ_{g ∈ T} ‖χ(g)‖²`, expanded through the identity of Lemma 2.4 on `T`. -/
theorem sum_TfinH_chi_mul_star (C : Sec2Ctx G) [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) :
    (∑ g ∈ TfinH C, χ (g : G) * star (χ (g : G))) =
      ∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
        chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
          chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
          (∑ g ∈ TfinH C,
            (ν : ClassFunction ↥C.P.H0 ℂ) g *
              star ((μ : ClassFunction ↥C.P.H0 ℂ) g)) := by
  classical
  have h1 : ∀ g ∈ TfinH C, χ (g : G) = ∑ ν : IrreducibleCharacter ↥C.P.H0,
      chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) * (ν : ClassFunction ↥C.P.H0 ℂ) g :=
    fun g hg => chi_expand_T C f hf χ hχ g (by rwa [mem_TfinH] at hg)
  have h2 : ∀ g ∈ TfinH C, star (χ (g : G)) = ∑ μ : IrreducibleCharacter ↥C.P.H0,
      chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
        star ((μ : ClassFunction ↥C.P.H0 ℂ) g) := by
    intro g hg
    rw [h1 g hg, star_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [star_mul, star_chiCoef C f hf χ hχ μ]
    ring
  calc (∑ g ∈ TfinH C, χ (g : G) * star (χ (g : G)))
      = ∑ g ∈ TfinH C, (∑ ν : IrreducibleCharacter ↥C.P.H0,
            chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
              (ν : ClassFunction ↥C.P.H0 ℂ) g) *
          (∑ μ : IrreducibleCharacter ↥C.P.H0,
            chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
              star ((μ : ClassFunction ↥C.P.H0 ℂ) g)) :=
        Finset.sum_congr rfl fun g hg => by rw [h2 g hg, h1 g hg]
    _ = ∑ g ∈ TfinH C, ∑ ν : IrreducibleCharacter ↥C.P.H0,
          ∑ μ : IrreducibleCharacter ↥C.P.H0,
            chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
              chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
              ((ν : ClassFunction ↥C.P.H0 ℂ) g *
                star ((μ : ClassFunction ↥C.P.H0 ℂ) g)) :=
        Finset.sum_congr rfl fun g _ => by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun ν _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun μ _ => ?_
          ring
    _ = ∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
          chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
            chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
            (∑ g ∈ TfinH C,
              (ν : ClassFunction ↥C.P.H0 ℂ) g *
                star ((μ : ClassFunction ↥C.P.H0 ℂ) g)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.mul_sum]

/-! ## 6. The `U`-sum through Remark 3.1 and the `\Lambda`-orbit structure -/

/-- The inner product of the restrictions of `ν` and `μ` to `U`. -/
noncomputable def innerU (C : Sec2Ctx G) [Fintype ↥C.P.H0] [Fintype ↥(Uin C)]
    [Invertible (Nat.card ↥(Uin C) : ℂ)] (ν μ : IrreducibleCharacter ↥C.P.H0) : ℂ :=
  ClassFunction.inner (ClassFunction.restrict (Uin C) (ν : ClassFunction ↥C.P.H0 ℂ))
    (ClassFunction.restrict (Uin C) (μ : ClassFunction ↥C.P.H0 ℂ))

/-- The indicator of `Λ`-equivalence, as a complex number (so that statements do not carry
decidability instances). -/
noncomputable def sameLam (C : Sec2Ctx G) (ν μ : ClassFunction ↥C.P.H0 ℂ) : ℂ := by
  classical exact if LamEquiv C ν μ then 1 else 0

/-- `c_ν = 1` if `ν^s ∈ Λν` and `ν^s ≠ ν`, and `c_ν = 0` otherwise. -/
noncomputable def cOrbit (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) : ℂ := by
  classical exact if LamEquiv C ν (sconj C ν) ∧ sconj C ν ≠ ν then 1 else 0

theorem sameLam_eq_one (C : Sec2Ctx G) {ν μ : ClassFunction ↥C.P.H0 ℂ}
    (h : LamEquiv C ν μ) : sameLam C ν μ = 1 := by
  classical rw [sameLam, if_pos h]

theorem sameLam_eq_zero (C : Sec2Ctx G) {ν μ : ClassFunction ↥C.P.H0 ℂ}
    (h : ¬ LamEquiv C ν μ) : sameLam C ν μ = 0 := by
  classical rw [sameLam, if_neg h]

theorem sameLam_self (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) : sameLam C ν ν = 1 :=
  sameLam_eq_one C (s02c_LamEquiv_refl C ν)

theorem cOrbit_val (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    cOrbit C ν = 0 ∨ cOrbit C ν = 1 := by
  classical
  by_cases h : LamEquiv C ν (sconj C ν) ∧ sconj C ν ≠ ν
  · right; rw [cOrbit, if_pos h]
  · left; rw [cOrbit, if_neg h]

/-- `c_ν = 1` exactly when `ν^s ∈ Λν` and `ν^s ≠ ν`. -/
theorem cOrbit_eq_one {C : Sec2Ctx G} {ν : ClassFunction ↥C.P.H0 ℂ}
    (h1 : LamEquiv C ν (sconj C ν)) (h2 : sconj C ν ≠ ν) : cOrbit C ν = 1 := by
  classical rw [cOrbit, if_pos ⟨h1, h2⟩]

theorem cOrbit_eq_zero {C : Sec2Ctx G} {ν : ClassFunction ↥C.P.H0 ℂ}
    (h : ¬ (LamEquiv C ν (sconj C ν) ∧ sconj C ν ≠ ν)) : cOrbit C ν = 0 := by
  classical rw [cOrbit, if_neg h]

/-- `Λ`-equivalent characters span the same `Λ`-orbit. -/
theorem lamOrbit_eq_of_lamEquiv {C : Sec2Ctx G} {ν μ : ClassFunction ↥C.P.H0 ℂ}
    (h : LamEquiv C ν μ) : lamOrbit C ν = lamOrbit C μ := by
  ext χ
  exact ⟨fun hχ => s02c_LamEquiv_trans C (s02c_LamEquiv_symm C h) hχ,
    fun hχ => s02c_LamEquiv_trans C h hχ⟩

/-- **Remark 3.1** in the usable orientation: the `U`-inner product of two `Λ`-equivalent
irreducible characters of `H₀` is `n/|Λμ|`. -/
theorem innerU_lamEquiv (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    [Fintype ↥C.P.H0] [Fintype ↥(Uin C)] [Invertible (Nat.card ↥(Uin C) : ℂ)]
    {ν μ : IrreducibleCharacter ↥C.P.H0}
    (h : LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ) (μ : ClassFunction ↥C.P.H0 ℂ)) :
    innerU C ν μ = (D.n : ℂ) / ((lamOrbit C (μ : ClassFunction ↥C.P.H0 ℂ)).ncard : ℂ) :=
  (((rem31Orth D C) hDC ν μ ν.2 μ.2).1 h)

/-- **Remark 3.1**, vanishing orientation. -/
theorem innerU_not_lamEquiv (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    [Fintype ↥C.P.H0] [Fintype ↥(Uin C)] [Invertible (Nat.card ↥(Uin C) : ℂ)]
    {ν μ : IrreducibleCharacter ↥C.P.H0}
    (h : ¬ LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ) (μ : ClassFunction ↥C.P.H0 ℂ)) :
    innerU C ν μ = 0 :=
  (((rem31Orth D C) hDC ν μ ν.2 μ.2).2 h)

/-- `innerU`, written with `sameLam` and the orbit size. -/
theorem innerU_eq (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C) [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] [Fintype ↥(Uin C)]
    [Invertible (Nat.card ↥(Uin C) : ℂ)] (ν μ : IrreducibleCharacter ↥C.P.H0) :
    innerU C ν μ = sameLam C (ν : ClassFunction ↥C.P.H0 ℂ) (μ : ClassFunction ↥C.P.H0 ℂ) *
      ((D.n : ℂ) / ((lamOrbit C (μ : ClassFunction ↥C.P.H0 ℂ)).ncard : ℂ)) := by
  classical
  by_cases h : LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ) (μ : ClassFunction ↥C.P.H0 ℂ)
  · rw [innerU_lamEquiv D C hDC h, sameLam_eq_one C h, one_mul]
  · rw [innerU_not_lamEquiv D C hDC h, sameLam_eq_zero C h, zero_mul]

/-- `𝒮(χ)` meets the `Λ`-orbit of `ν` in at most the pair `{ν, ν^s}`
(`Work.BG.bset_orbit_struct`). -/
theorem bset_orbit_subset (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) (ν : IrreducibleCharacter ↥C.P.H0)
    (hν : (ν : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ)
    (μ : IrreducibleCharacter ↥C.P.H0) (hμ : (μ : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ)
    (hlam : LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ) (μ : ClassFunction ↥C.P.H0 ℂ))
    (hne : μ ≠ ν) :
    (μ : ClassFunction ↥C.P.H0 ℂ) = sconj C (ν : ClassFunction ↥C.P.H0 ℂ) :=
  (bset_orbit_struct C f hf χ hχ).2 ν hν μ hμ hlam (fun h => hne (Subtype.ext h))

/-- The sum of `e_μ` over the `Λ`-orbit of `ν ∈ 𝒮(χ)` is `e_ν (1 + c_ν)`. -/
theorem sum_sameLam (C : Sec2Ctx G) [Fintype ↥C.P.H0] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) (ν : IrreducibleCharacter ↥C.P.H0)
    (hν : chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) ≠ 0) :
    (∑ μ : IrreducibleCharacter ↥C.P.H0,
        sameLam C (ν : ClassFunction ↥C.P.H0 ℂ) (μ : ClassFunction ↥C.P.H0 ℂ) *
          chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ)) =
      chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
        (1 + cOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)) := by
  classical
  have hbs := bset_orbit_struct C f hf χ hχ
  have hvmem : (ν : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ := ⟨ν.2, hν⟩
  obtain ⟨ρ, hρv⟩ : ∃ ρ : IrreducibleCharacter ↥C.P.H0,
      (ρ : ClassFunction ↥C.P.H0 ℂ) = sconj C (ν : ClassFunction ↥C.P.H0 ℂ) :=
    ⟨⟨sconj C (ν : ClassFunction ↥C.P.H0 ℂ),
      Work.BG.IsIrreducibleCharacter.conjByH C.P C.s ν.2⟩, rfl⟩
  set s0 : Finset (IrreducibleCharacter ↥C.P.H0) :=
    Finset.univ.filter (fun μ => LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ)
      (μ : ClassFunction ↥C.P.H0 ℂ)) with hs0
  set s1 : Finset (IrreducibleCharacter ↥C.P.H0) :=
    s0.filter (fun μ => chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) ≠ 0) with hs1
  have hmem_s1 : ∀ μ : IrreducibleCharacter ↥C.P.H0, μ ∈ s1 ↔
      LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ) (μ : ClassFunction ↥C.P.H0 ℂ) ∧
        chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) ≠ 0 := by
    intro μ
    rw [hs1, hs0]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  -- in the orbit, only `ν` and `ν^s` can have `e ≠ 0`
  have hkey : ∀ μ ∈ s1, μ = ν ∨ μ = ρ := by
    intro μ hμ
    rcases (hmem_s1 μ).mp hμ with ⟨hlam, he⟩
    by_cases hμν : μ = ν
    · exact Or.inl hμν
    · refine Or.inr (Subtype.ext ?_)
      exact (bset_orbit_subset C f hf χ hχ ν hvmem μ ⟨μ.2, he⟩ hlam hμν).trans hρv.symm
  -- step 1: rewrite the sum as a sum over the `Λ`-orbit
  have hstep : (∑ μ : IrreducibleCharacter ↥C.P.H0,
        sameLam C (ν : ClassFunction ↥C.P.H0 ℂ) (μ : ClassFunction ↥C.P.H0 ℂ) *
          chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ)) =
      ∑ μ ∈ s0, chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) := by
    rw [hs0, Finset.sum_filter]
    refine Finset.sum_congr rfl fun μ _ => ?_
    by_cases h : LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ) (μ : ClassFunction ↥C.P.H0 ℂ)
    · rw [sameLam_eq_one C h, if_pos h, one_mul]
    · rw [sameLam_eq_zero C h, if_neg h, zero_mul]
  -- step 2: drop the vanishing terms
  have hstep2 : (∑ μ ∈ s0, chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ)) =
      ∑ μ ∈ s1, chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) := by
    rw [hs1]
    exact (Finset.sum_subset (Finset.filter_subset _ _) fun x hx hx' => by
      exact by_contra fun hne => hx' (Finset.mem_filter.mpr ⟨hx, hne⟩)).symm
  rw [hstep, hstep2]
  -- case analysis
  rcases eq_or_ne (sconj C (ν : ClassFunction ↥C.P.H0 ℂ))
    (ν : ClassFunction ↥C.P.H0 ℂ) with hfix | hne
  · -- `ν^s = ν`: only `ν` itself contributes
    have hs1eq : s1 = {ν} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
      · rw [hmem_s1]; exact ⟨s02c_LamEquiv_refl C _, hν⟩
      · intro b hb
        rcases hkey b hb with h | h
        · exact h
        · exact h.trans (Subtype.ext (by
            change (ρ : ClassFunction ↥C.P.H0 ℂ) = (ν : ClassFunction ↥C.P.H0 ℂ)
            rw [hρv, hfix]))
    rw [hs1eq, Finset.sum_singleton,
      show cOrbit C (ν : ClassFunction ↥C.P.H0 ℂ) = 0 from
        cOrbit_eq_zero fun h => h.2 hfix,
      add_zero, mul_one]
  · by_cases hlei : LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ)
        (sconj C (ν : ClassFunction ↥C.P.H0 ℂ))
    · -- `ν^s ∈ Λν`, `ν^s ≠ ν`: `ν` and `ν^s` contribute
      have hρs1 : ρ ∈ s1 := by
        rw [hmem_s1, hρv]
        refine ⟨hlei, ?_⟩
        have hfs : f (sconj C (ν : ClassFunction ↥C.P.H0 ℂ)) =
            f (ν : ClassFunction ↥C.P.H0 ℂ) := (hbs.1 _ hvmem).2.1
        rw [chiCoef, hfs]
        exact hν
      have hs1eq : s1 = insert ν {ρ} := by
        refine Finset.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
        · rcases hkey x hx with h | h
          · rw [h]; exact Finset.mem_insert_self _ _
          · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        · rw [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h
          · rw [h]
            rw [hmem_s1]; exact ⟨s02c_LamEquiv_refl C _, hν⟩
          · rw [h]; exact hρs1
      have hνρ : ν ≠ ρ := fun h =>
        hne (hρv.symm.trans (congrArg Subtype.val h).symm)
      rw [hs1eq, Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hνρ),
        Finset.sum_singleton]
      have heρ : chiCoef C f χ (ρ : ClassFunction ↥C.P.H0 ℂ) =
          chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) := by
        rw [chiCoef, chiCoef, hρv, (hbs.1 (ν : ClassFunction ↥C.P.H0 ℂ) hvmem).2.1]
      rw [heρ, show cOrbit C (ν : ClassFunction ↥C.P.H0 ℂ) = 1 from cOrbit_eq_one hlei hne]
      ring
    · -- `ν^s ∉ Λν`: only `ν` contributes
      have hs1eq : s1 = {ν} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
        · rw [hmem_s1]; exact ⟨s02c_LamEquiv_refl C _, hν⟩
        · intro b hb
          rcases hkey b hb with h | h
          · exact h
          · exfalso
            rw [h] at hb
            rcases (hmem_s1 ρ).mp hb with ⟨hlam, -⟩
            rw [hρv] at hlam
            exact hlei hlam
      rw [hs1eq, Finset.sum_singleton,
        show cOrbit C (ν : ClassFunction ↥C.P.H0 ℂ) = 0 from
          cOrbit_eq_zero fun h => hlei h.1,
        add_zero, mul_one]

/-- The complex number `Σ_{ν} e_ν² (1 + c_ν)/|Λν|` of the proof of Theorem 3.2. -/
noncomputable def Ssum (C : Sec2Ctx G) [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (χ : ClassFunction G ℂ) : ℂ :=
  ∑ ν : IrreducibleCharacter ↥C.P.H0,
    chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
      chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
      (1 + cOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)) /
      ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℂ)

/-- `Σ_ν e_ν² = |𝒮(χ)|`. -/
theorem sum_chiCoef_sq (C : Sec2Ctx G) [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) :
    (∑ ν : IrreducibleCharacter ↥C.P.H0,
        chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
          chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ)) =
      ((bset C f χ).ncard : ℂ) := by
  classical
  have hfin := s02_bset_finite C f χ
  have hterm : ∀ ν : IrreducibleCharacter ↥C.P.H0,
      chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
        chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) =
      if (ν : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ then 1 else 0 := by
    intro ν
    by_cases h : (ν : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ
    · rcases (bset_orbit_struct C f hf χ hχ).1 _ h |>.2.2 with hh | hh
      · rw [if_pos h]; simp only [chiCoef]; rw [hh]; ring
      · rw [if_pos h]; simp only [chiCoef]; rw [hh]; ring
    · have hz : chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) = 0 := by
        by_contra hc
        exact h ⟨ν.2, hc⟩
      rw [if_neg h, hz]; ring
  rw [s02_sum_irr_eq_finsum_bset C f χ
    (fun ξ : ClassFunction ↥C.P.H0 ℂ => chiCoef C f χ ξ * chiCoef C f χ ξ) (fun ν hν => by
      have hz : chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) = 0 := by
        by_contra hc
        exact hν ⟨ν.2, hc⟩
      rw [hz]; ring)]
  rw [finsum_mem_eq_finite_toFinset_sum
    (fun ξ : ClassFunction ↥C.P.H0 ℂ => chiCoef C f χ ξ * chiCoef C f χ ξ) hfin]
  have hone : ∀ ξ ∈ hfin.toFinset, chiCoef C f χ ξ * chiCoef C f χ ξ = 1 := by
    intro ξ hξ
    have hb : ξ ∈ bset C f χ := (Set.Finite.mem_toFinset hfin).mp hξ
    exact (hterm ⟨ξ, hb.1⟩).trans (if_pos hb)
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one,
    Set.ncard_eq_toFinset_card (bset C f χ) hfin]

/-- The double sum over the `U`-inner products, grouped into `Λ`-orbits. -/
theorem sum_innerU_eq (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C) [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] [Fintype ↥(Uin C)]
    [Invertible (Nat.card ↥(Uin C) : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) :
    (∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
        chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
          chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) * innerU C ν μ) =
      (D.n : ℂ) * Ssum C f χ := by
  classical
  have hA : ∀ ν : IrreducibleCharacter ↥C.P.H0,
      chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) ≠ 0 →
      (∑ μ : IrreducibleCharacter ↥C.P.H0,
          chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) * innerU C ν μ) =
        chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
          (1 + cOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)) *
          ((D.n : ℂ) / ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℂ)) := by
    intro ν hν
    have h1 : ∀ μ : IrreducibleCharacter ↥C.P.H0,
        chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) * innerU C ν μ =
          (chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
            sameLam C (ν : ClassFunction ↥C.P.H0 ℂ) (μ : ClassFunction ↥C.P.H0 ℂ)) *
            ((D.n : ℂ) / ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℂ)) := by
      intro μ
      by_cases h : LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ) (μ : ClassFunction ↥C.P.H0 ℂ)
      · rw [innerU_lamEquiv D C hDC h, ← lamOrbit_eq_of_lamEquiv h, sameLam_eq_one C h]
        ring
      · rw [innerU_not_lamEquiv D C hDC h, sameLam_eq_zero C h]
        ring
    have h2 : (∑ μ : IrreducibleCharacter ↥C.P.H0,
        chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
          sameLam C (ν : ClassFunction ↥C.P.H0 ℂ) (μ : ClassFunction ↥C.P.H0 ℂ)) =
        chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
          (1 + cOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)) := by
      rw [show (∑ μ : IrreducibleCharacter ↥C.P.H0,
            chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
              sameLam C (ν : ClassFunction ↥C.P.H0 ℂ) (μ : ClassFunction ↥C.P.H0 ℂ)) =
          ∑ μ : IrreducibleCharacter ↥C.P.H0,
            sameLam C (ν : ClassFunction ↥C.P.H0 ℂ) (μ : ClassFunction ↥C.P.H0 ℂ) *
              chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) from
        Finset.sum_congr rfl fun μ _ => mul_comm _ _]
      exact sum_sameLam C f hf χ hχ ν hν
    calc (∑ μ : IrreducibleCharacter ↥C.P.H0,
          chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) * innerU C ν μ)
        = ∑ μ : IrreducibleCharacter ↥C.P.H0,
            (chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
              sameLam C (ν : ClassFunction ↥C.P.H0 ℂ) (μ : ClassFunction ↥C.P.H0 ℂ)) *
              ((D.n : ℂ) / ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℂ)) :=
          Finset.sum_congr rfl fun μ _ => h1 μ
      _ = (∑ μ : IrreducibleCharacter ↥C.P.H0,
            chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
              sameLam C (ν : ClassFunction ↥C.P.H0 ℂ) (μ : ClassFunction ↥C.P.H0 ℂ)) *
            ((D.n : ℂ) / ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℂ)) := by
          rw [Finset.sum_mul]
      _ = chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
            (1 + cOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)) *
            ((D.n : ℂ) / ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℂ)) := by
          rw [h2]
  have key : ∀ ν : IrreducibleCharacter ↥C.P.H0,
      chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
        (∑ μ : IrreducibleCharacter ↥C.P.H0,
          chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) * innerU C ν μ) =
      chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
        (chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
          (1 + cOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)) *
          ((D.n : ℂ) / ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℂ))) := by
    intro ν
    by_cases h : chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) = 0
    · rw [h, zero_mul, zero_mul]
    · rw [hA ν h]
  calc (∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
        chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
          chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) * innerU C ν μ)
      = ∑ ν : IrreducibleCharacter ↥C.P.H0,
          chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
            (∑ μ : IrreducibleCharacter ↥C.P.H0,
              chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) * innerU C ν μ) := by
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun μ _ => by ring
    _ = ∑ ν : IrreducibleCharacter ↥C.P.H0,
          chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
            (chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
              (1 + cOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)) *
              ((D.n : ℂ) / ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℂ))) :=
        Finset.sum_congr rfl fun ν _ => key ν
    _ = (D.n : ℂ) * Ssum C f χ := by
        rw [Ssum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ν _ => ?_
        have hq : ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℂ) ≠ 0 := by
          have hfin : (lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).Finite := orbit_finite C _
          have hpos : 0 < (lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard :=
            (Set.ncard_pos hfin).mpr ⟨_, s02c_LamEquiv_refl C _⟩
          exact Nat.cast_ne_zero.mpr hpos.ne'
        field_simp

/-- `|U| · n = |H₀|` (`n = [H₀ : U]`, the paper's `m`). -/
theorem card_Uin_mul_n (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C) :
    (Nat.card ↥(Uin C) : ℂ) * (D.n : ℂ) = (Nat.card ↥C.P.H0 : ℂ) := by
  have h2 : Nat.card ↥(Uin C) * (Uin C).index = Nat.card ↥C.P.H0 :=
    Subgroup.card_mul_index _
  rw [← rem31IndexUin D C hDC]
  exact_mod_cast h2

/-- **The main identity.**  `Σ_{g ∈ T} |χ(g)|² = |H₀| · (|𝒮(χ)| - Σ_ν e_ν²(1+c_ν)/|Λν|)`. -/
theorem chi_sum_T_eq (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C) [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] [Fintype ↥(Uin C)]
    [Invertible (Nat.card ↥(Uin C) : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) :
    (∑ g ∈ TfinH C, χ (g : G) * star (χ (g : G))) =
      (Nat.card ↥C.P.H0 : ℂ) * (((bset C f χ).ncard : ℂ) - Ssum C f χ) := by
  classical
  have hsplit : ∀ ν μ : IrreducibleCharacter ↥C.P.H0,
      (∑ g ∈ TfinH C,
          (ν : ClassFunction ↥C.P.H0 ℂ) g * star ((μ : ClassFunction ↥C.P.H0 ℂ) g)) =
        (∑ g : ↥C.P.H0,
          (ν : ClassFunction ↥C.P.H0 ℂ) g * star ((μ : ClassFunction ↥C.P.H0 ℂ) g)) -
        (∑ g ∈ UfinH C,
          (ν : ClassFunction ↥C.P.H0 ℂ) g * star ((μ : ClassFunction ↥C.P.H0 ℂ) g)) := by
    intro ν μ
    rw [sum_univ_eq_sum_TfinH_add_sum_UfinH C
      (fun g : ↥C.P.H0 =>
        (ν : ClassFunction ↥C.P.H0 ℂ) g * star ((μ : ClassFunction ↥C.P.H0 ℂ) g))]
    ring
  rw [sum_TfinH_chi_mul_star C f hf χ hχ]
  have hstep : (∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
        chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
          chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
          (∑ g ∈ TfinH C, (ν : ClassFunction ↥C.P.H0 ℂ) g *
            star ((μ : ClassFunction ↥C.P.H0 ℂ) g))) =
      ∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
        chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
          chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
          ((∑ g : ↥C.P.H0, (ν : ClassFunction ↥C.P.H0 ℂ) g *
              star ((μ : ClassFunction ↥C.P.H0 ℂ) g)) -
            (∑ g ∈ UfinH C, (ν : ClassFunction ↥C.P.H0 ℂ) g *
              star ((μ : ClassFunction ↥C.P.H0 ℂ) g))) := by
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
    rw [hsplit ν μ]
  rw [hstep]
  -- distribute the difference
  have hdist : (∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
        chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
          chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
          ((∑ g : ↥C.P.H0, (ν : ClassFunction ↥C.P.H0 ℂ) g *
              star ((μ : ClassFunction ↥C.P.H0 ℂ) g)) -
            (∑ g ∈ UfinH C, (ν : ClassFunction ↥C.P.H0 ℂ) g *
              star ((μ : ClassFunction ↥C.P.H0 ℂ) g)))) =
      (∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
          chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
            chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
            (∑ g : ↥C.P.H0, (ν : ClassFunction ↥C.P.H0 ℂ) g *
              star ((μ : ClassFunction ↥C.P.H0 ℂ) g))) -
        (∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
          chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
            chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
            (∑ g ∈ UfinH C, (ν : ClassFunction ↥C.P.H0 ℂ) g *
              star ((μ : ClassFunction ↥C.P.H0 ℂ) g))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun μ _ => by ring
  rw [hdist]
  -- the `H₀` part: orthonormality
  have hA : (∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
        chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
          chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
          (∑ g : ↥C.P.H0, (ν : ClassFunction ↥C.P.H0 ℂ) g *
            star ((μ : ClassFunction ↥C.P.H0 ℂ) g))) =
      (Nat.card ↥C.P.H0 : ℂ) *
        (∑ ν : IrreducibleCharacter ↥C.P.H0,
          chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
            chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ)) := by
    have h2 : (∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
        chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
          chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
          (∑ g : ↥C.P.H0, (ν : ClassFunction ↥C.P.H0 ℂ) g *
            star ((μ : ClassFunction ↥C.P.H0 ℂ) g))) =
        ∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
          chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
            chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
            ((Nat.card ↥C.P.H0 : ℂ) *
              ClassFunction.inner (ν : ClassFunction ↥C.P.H0 ℂ)
                (μ : ClassFunction ↥C.P.H0 ℂ)) :=
      Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => by
        rw [sum_univ_mul_star C ν μ]
    have h3 : (∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
          chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
            chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
            ((Nat.card ↥C.P.H0 : ℂ) *
              ClassFunction.inner (ν : ClassFunction ↥C.P.H0 ℂ)
                (μ : ClassFunction ↥C.P.H0 ℂ))) =
        ∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
          chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
            chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
            ((Nat.card ↥C.P.H0 : ℂ) * (if ν = μ then 1 else 0)) :=
      Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => by
        rw [irreducibleCharacter_inner_eq_ite]
    have h4 : (∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
          chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
            chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
            ((Nat.card ↥C.P.H0 : ℂ) * (if ν = μ then 1 else 0))) =
        ∑ ν : IrreducibleCharacter ↥C.P.H0,
          chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
            (chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) * (Nat.card ↥C.P.H0 : ℂ)) :=
      Finset.sum_congr rfl fun ν _ => by
        rw [Finset.sum_eq_single ν]
        · rw [if_pos rfl]; ring
        · intro μ _ hμν
          rw [if_neg (fun h : ν = μ => hμν h.symm)]
          ring
        · intro h
          exact absurd (Finset.mem_univ ν) h
    have h5 : (∑ ν : IrreducibleCharacter ↥C.P.H0,
          chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
            (chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) * (Nat.card ↥C.P.H0 : ℂ))) =
        (Nat.card ↥C.P.H0 : ℂ) *
          (∑ ν : IrreducibleCharacter ↥C.P.H0,
            chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
              chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ν _ => by ring
    exact h2.trans (h3.trans (h4.trans h5))
  -- the `U` part: Remark 3.1
  have hB : (∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
        chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
          chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
          (∑ g ∈ UfinH C, (ν : ClassFunction ↥C.P.H0 ℂ) g *
            star ((μ : ClassFunction ↥C.P.H0 ℂ) g))) =
      (Nat.card ↥(Uin C) : ℂ) *
        (∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
          chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
            chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) * innerU C ν μ) := by
    have h2 : (∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
        chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
          chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
          (∑ g ∈ UfinH C, (ν : ClassFunction ↥C.P.H0 ℂ) g *
            star ((μ : ClassFunction ↥C.P.H0 ℂ) g))) =
        ∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
          chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
            chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
            ((Nat.card ↥(Uin C) : ℂ) * innerU C ν μ) :=
      Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => by
        rw [sum_UfinH_mul_star C ν μ]
        rfl
    have h3 : (∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
          chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
            chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) *
            ((Nat.card ↥(Uin C) : ℂ) * innerU C ν μ)) =
        (Nat.card ↥(Uin C) : ℂ) *
          (∑ ν : IrreducibleCharacter ↥C.P.H0, ∑ μ : IrreducibleCharacter ↥C.P.H0,
            chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
              chiCoef C f χ (μ : ClassFunction ↥C.P.H0 ℂ) * innerU C ν μ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun μ _ => by ring
    exact h2.trans h3
  rw [hA, hB, sum_chiCoef_sq C f hf χ hχ, sum_innerU_eq D C hDC f hf χ hχ,
    show (Nat.card ↥(Uin C) : ℂ) * ((D.n : ℂ) * Ssum C f χ)
      = (Nat.card ↥C.P.H0 : ℂ) * Ssum C f χ from by
        rw [← mul_assoc, card_Uin_mul_n D C hDC]]
  ring

/-! ## 7. The size of a `Λ`-orbit -/

/-- Real version of `cOrbit`. -/
noncomputable def cOrbitR (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) : ℝ := by
  classical exact if LamEquiv C ν (sconj C ν) ∧ sconj C ν ≠ ν then 1 else 0

/-- The indicator of `𝒮(χ)`, as a real number. -/
noncomputable def bsetInd (C : Sec2Ctx G) [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (χ : ClassFunction G ℂ)
    (ν : IrreducibleCharacter ↥C.P.H0) : ℝ := by
  classical exact if (ν : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ then 1 else 0

@[simp] theorem bsetInd_of_mem {C : Sec2Ctx G} [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] {f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ}
    {χ : ClassFunction G ℂ} {ν : IrreducibleCharacter ↥C.P.H0}
    (h : (ν : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ) : bsetInd C f χ ν = 1 := by
  classical rw [bsetInd, if_pos h]

@[simp] theorem bsetInd_of_notMem {C : Sec2Ctx G} [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] {f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ}
    {χ : ClassFunction G ℂ} {ν : IrreducibleCharacter ↥C.P.H0}
    (h : (ν : ClassFunction ↥C.P.H0 ℂ) ∉ bset C f χ) : bsetInd C f χ ν = 0 := by
  classical rw [bsetInd, if_neg h]

theorem cOrbit_eq_ofReal (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    cOrbit C ν = ((cOrbitR C ν : ℝ) : ℂ) := by
  classical
  by_cases h : LamEquiv C ν (sconj C ν) ∧ sconj C ν ≠ ν
  · rw [cOrbit_eq_one h.1 h.2, cOrbitR, if_pos h]; norm_num
  · rw [cOrbit_eq_zero h, cOrbitR, if_neg h]; norm_num

/-- Every `Λ`-orbit of an irreducible character has at least two elements. -/
theorem lamOrbit_card_ge_two (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (ν : ClassFunction ↥C.P.H0 ℂ) (hν : IsIrreducibleCharacter ν) :
    2 ≤ (lamOrbit C ν).ncard := by
  classical
  obtain ⟨β, hβ⟩ := s02_exists_lamCF_apply_t_eq_neg_one C
  have hne : lamCF C β * ν ≠ ν := by
    intro h
    have h1 : (lamCF C β * ν) C.t = ν C.t := by rw [h]
    rw [ClassFunction.mul_apply, hβ, neg_one_mul] at h1
    refine value_t_ne_zero C ν hν ?_
    have h2 : ν C.t + ν C.t = 0 := by
      calc ν C.t + ν C.t = -ν C.t + ν C.t := by rw [h1]
        _ = 0 := by ring
    have h3 : (2 : ℂ) * ν C.t = 0 := by rw [two_mul]; exact h2
    exact (mul_eq_zero.mp h3).resolve_left two_ne_zero
  have hsub : ({ν, lamCF C β * ν} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ lamOrbit C ν := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h
    · rw [h]; exact mem_lamOrbit_self C ν
    · rw [h]; exact ⟨β, rfl⟩
  have hpair : ({ν, lamCF C β * ν} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 2 :=
    Set.ncard_pair (Ne.symm hne)
  calc 2 = ({ν, lamCF C β * ν} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard := hpair.symm
    _ ≤ (lamOrbit C ν).ncard := Set.ncard_le_ncard hsub (orbit_finite C ν)

/-- An `s`-stable `Λ`-orbit containing a non-`s`-fixed character has at least four elements
(BG Lemma 2.1: exactly two members of a stable orbit are `s`-fixed). -/
theorem lamOrbit_card_ge_four (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν)
    (hmem : LamEquiv C ν (sconj C ν)) (hne : sconj C ν ≠ ν) :
    4 ≤ (lamOrbit C ν).ncard := by
  classical
  have hfix := (s02_lemma21 C ν hν).2 (by
    rw [s02c_sconj_image_lamOrbit C (sconjLam C) ν, lamOrbit_eq_of_lamEquiv hmem])
  have hfin : (lamOrbit C ν).Finite := orbit_finite C ν
  have hsν : sconj C ν ∈ lamOrbit C ν := hmem
  have hdisj : Disjoint ({χ ∈ lamOrbit C ν | sconj C χ = χ} : Set (ClassFunction ↥C.P.H0 ℂ))
      ({ν, sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx⟩ (h | h)
    · exact hne (h ▸ hx)
    · refine hne ?_
      have h2 := hx
      rw [h, sconj_sconj] at h2
      exact h2.symm
  have hsub : ({χ ∈ lamOrbit C ν | sconj C χ = χ} : Set (ClassFunction ↥C.P.H0 ℂ)) ∪
      ({ν, sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ lamOrbit C ν := by
    intro x hx
    rcases hx with hx | hx
    · exact hx.1
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h
      · rw [h]; exact mem_lamOrbit_self C ν
      · rw [h]; exact hsν
  have hfin' : ({χ ∈ lamOrbit C ν | sconj C χ = χ} : Set (ClassFunction ↥C.P.H0 ℂ)).Finite :=
    hfin.subset fun _ hx => hx.1
  have hfin'' : ({ν, sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ)).Finite :=
    (Set.finite_singleton (sconj C ν)).insert ν
  calc 4 = ({χ ∈ lamOrbit C ν | sconj C χ = χ} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard +
        ({ν, sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard := by
        rw [hfix, Set.ncard_pair (Ne.symm hne)]
    _ = (({χ ∈ lamOrbit C ν | sconj C χ = χ} : Set (ClassFunction ↥C.P.H0 ℂ)) ∪
        ({ν, sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ))).ncard :=
        (Set.ncard_union_eq hdisj hfin' hfin'').symm
    _ ≤ (lamOrbit C ν).ncard := Set.ncard_le_ncard hsub hfin

/-! ## 8. The bound `Σ_ν e_ν²(1+c_ν)/|Λν| ≤ |𝒮(χ)|/2` -/

/-- `e_ν²` is `1` on `𝒮(χ)` and `0` off it. -/
theorem chiCoef_sq_eq (C : Sec2Ctx G) [Fintype ↥C.P.H0] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) (ν : IrreducibleCharacter ↥C.P.H0) :
    chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) * chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) =
      ((bsetInd C f χ ν : ℝ) : ℂ) := by
  classical
  by_cases h : (ν : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ
  · rcases (bset_orbit_struct C f hf χ hχ).1 _ h |>.2.2 with hh | hh
    · rw [bsetInd_of_mem h]; simp only [chiCoef]; rw [hh]; norm_num
    · rw [bsetInd_of_mem h]; simp only [chiCoef]; rw [hh]; norm_num
  · have hz : chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) = 0 := by
      by_contra hc
      exact h ⟨ν.2, hc⟩
    rw [bsetInd_of_notMem h, hz]; norm_num

/-- Each summand of `Ssum` is the coercion of a real number. -/
theorem Ssum_term_ofReal (C : Sec2Ctx G) [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) (ν : IrreducibleCharacter ↥C.P.H0) :
    chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
        chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) * (1 + cOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)) /
        ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℂ) =
      ((((bsetInd C f χ ν) *
          (1 + cOrbitR C (ν : ClassFunction ↥C.P.H0 ℂ))) /
          ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ) : ℝ) : ℂ) := by
  rw [chiCoef_sq_eq C f hf χ hχ ν, cOrbit_eq_ofReal]
  rw [show (1 : ℂ) + ((cOrbitR C (ν : ClassFunction ↥C.P.H0 ℂ) : ℝ) : ℂ) =
      (((1 + cOrbitR C (ν : ClassFunction ↥C.P.H0 ℂ)) : ℝ) : ℂ) from
    (Complex.ofReal_add 1 _).symm]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_div]

/-- **The bound** `2 · Re Σ_ν e_ν²(1+c_ν)/|Λν| ≤ |𝒮(χ)|`. -/
theorem two_re_Ssum_le (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C) [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) :
    2 * (Ssum C f χ).re ≤ ((bset C f χ).ncard : ℝ) := by
  classical
  have hterm : ∀ ν : IrreducibleCharacter ↥C.P.H0,
      2 * (chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
          chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
          (1 + cOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)) /
          ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℂ)).re ≤
        bsetInd C f χ ν := by
    intro ν
    have hn : (0 : ℝ) < ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ) := by
      have hfin : (lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).Finite := orbit_finite C _
      exact_mod_cast (Set.ncard_pos hfin).mpr ⟨_, s02c_LamEquiv_refl C _⟩
    have hkey : ∀ k : ℝ, 2 * k ≤ ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ) →
        2 * (1 * k / ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ)) ≤ 1 := by
      intro k hk
      rw [mul_div_assoc', div_le_one hn, one_mul]
      exact hk
    rw [Ssum_term_ofReal C f hf χ hχ ν, Complex.ofReal_re]
    by_cases h : (ν : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ
    · rw [bsetInd_of_mem h]
      have hc : cOrbitR C (ν : ClassFunction ↥C.P.H0 ℂ) = 0 ∨
          cOrbitR C (ν : ClassFunction ↥C.P.H0 ℂ) = 1 := by
        rw [cOrbitR]
        split <;> [right; left] <;> norm_num
      rcases hc with hc | hc
      · have h1 := hkey (1 + 0) (by
          have h2 := lamOrbit_card_ge_two C (ν : ClassFunction ↥C.P.H0 ℂ) ν.2
          have h3 : (2 : ℝ) ≤ ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ) := by
            exact_mod_cast h2
          linarith)
        simpa [hc] using h1
      · have hmem : LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ)
            (sconj C (ν : ClassFunction ↥C.P.H0 ℂ)) := by
          by_contra hcon
          rw [cOrbitR, if_neg (fun hh => hcon hh.1)] at hc
          exact one_ne_zero hc.symm
        have hne' : sconj C (ν : ClassFunction ↥C.P.H0 ℂ) ≠ (ν : ClassFunction ↥C.P.H0 ℂ) := by
          intro hcon
          rw [cOrbitR, if_neg (fun hh => hh.2 hcon)] at hc
          exact one_ne_zero hc.symm
        have h1 := hkey (1 + 1) (by
          have h2 := lamOrbit_card_ge_four C ν.2 hmem hne'
          have h3 : (4 : ℝ) ≤ ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ) := by
            exact_mod_cast h2
          linarith)
        simpa [hc] using h1
    · rw [bsetInd_of_notMem h]
      simp

  calc 2 * (Ssum C f χ).re
      = (∑ ν : IrreducibleCharacter ↥C.P.H0, 2 *
          (chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
            chiCoef C f χ (ν : ClassFunction ↥C.P.H0 ℂ) *
            (1 + cOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)) /
            ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℂ)).re) := by
        rw [Ssum, Complex.re_sum, Finset.mul_sum]
    _ ≤ ∑ ν : IrreducibleCharacter ↥C.P.H0, bsetInd C f χ ν :=
        Finset.sum_le_sum fun ν _ => hterm ν
    _ = ((bset C f χ).ncard : ℝ) := by
        have hfin := s02_bset_finite C f χ
        have h1 : (∑ ν : IrreducibleCharacter ↥C.P.H0, bsetInd C f χ ν) =
            (((Finset.univ.filter
              (fun ν : IrreducibleCharacter ↥C.P.H0 =>
                (ν : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ)).card : ℕ) : ℝ) := by
          rw [← Finset.sum_boole
            (fun ν : IrreducibleCharacter ↥C.P.H0 =>
              (ν : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ) Finset.univ]
          refine Finset.sum_congr rfl fun ν _ => ?_
          by_cases h : (ν : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ <;>
            simp [bsetInd, h]
        rw [h1, Set.ncard_eq_toFinset_card (bset C f χ) hfin]
        congr 1
        refine Finset.card_bij (fun ν (_ : ν ∈ Finset.univ.filter
            (fun ν : IrreducibleCharacter ↥C.P.H0 =>
              (ν : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ)) =>
            (ν : ClassFunction ↥C.P.H0 ℂ)) ?_ ?_ ?_
        · intro ν hν
          exact (Set.Finite.mem_toFinset hfin).mpr (Finset.mem_filter.mp hν).2
        · intro a _ b _ hab
          exact Subtype.ext hab
        · intro ξ hξ
          refine ⟨⟨ξ, (Set.Finite.mem_toFinset hfin).mp hξ |>.1⟩, ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (Set.Finite.mem_toFinset hfin).mp hξ⟩

/-! ## 9. The TI-counting bound `(1/|H₀|)·Σ_T ‖χ‖² < 2` -/

/-- `Σ_{x ∈ G} ‖φ(x)‖² = |G|` for `φ ∈ ±Irr(G)`. -/
theorem normSq_sum_univ (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) :
    (∑ x : G, ‖χ x‖ ^ 2) = (Nat.card G : ℝ) := by
  have key : ∀ ψ : ClassFunction G ℂ, IsIrreducibleCharacter ψ →
      (∑ x : G, ‖ψ x‖ ^ 2) = (Nat.card G : ℝ) := by
    intro ψ hψ
    have h1 : (∑ x : G, ψ x * star (ψ x)) = (Nat.card G : ℂ) := by
      rw [show (∑ x : G, ψ x * star (ψ x)) = ClassFunction.innerSum ψ ψ from rfl,
        show ClassFunction.innerSum ψ ψ = (Nat.card G : ℂ) * ClassFunction.inner ψ ψ from
          (ClassFunction.card_mul_inner ψ ψ).symm,
        irreducibleCharacter_inner_eq_ite ⟨ψ, hψ⟩ ⟨ψ, hψ⟩, if_pos rfl, mul_one]
    have h2 : (((∑ x : G, ‖ψ x‖ ^ 2) : ℝ) : ℂ) = ∑ x : G, ψ x * star (ψ x) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.star_def, ← Complex.normSq_eq_norm_sq]
      exact (Complex.mul_conj (ψ x)).symm
    rw [← h2] at h1
    exact_mod_cast h1
  rcases hχ with h | h
  · exact key χ h
  · simpa using key (-χ) h

/-- `1 ∉ T^G`. -/
theorem one_notMem_TconjFin (C : Sec2Ctx G) : (1 : G) ∉ TconjFin C := by
  classical
  intro hmem
  rw [mem_TconjFin, OddOrder.GroupTheory.mem_conjClassSet] at hmem
  obtain ⟨t, ht, g, hg⟩ := hmem
  have ht1 : t = 1 := by
    have h : t = g⁻¹ * 1 * g := by rw [← hg]; group
    simpa using h
  exact ht.2 (ht1 ▸ C.P.U.one_mem)

/-- **The TI-counting bound**: `Σ_{g ∈ T} ‖χ(g)‖² < 2|H₀|`. -/
theorem sum_TfinH_normSq_lt (C : Sec2Ctx G) [Fintype ↥C.P.H0] (χ : ClassFunction G ℂ)
    (hχ : IsPmIrr χ) :
    (∑ g ∈ TfinH C, ‖χ (g : G)‖ ^ 2) < 2 * (Nat.card ↥C.P.H0 : ℝ) := by
  classical
  -- `T` is `H`-invariant
  have hstab : ∀ l ∈ C.P.H, MulAut.conj l • Tset C.P.H0 C.P.U = Tset C.P.H0 C.P.U := by
    intro l hl
    have hl' : ∀ x : G, x ∈ Tset C.P.H0 C.P.U ↔ l * x * l⁻¹ ∈ Tset C.P.H0 C.P.U :=
      C.P.le_normalizer_T hl
    ext x
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rw [MulAut.smul_def, MulAut.conj_apply] at hyx
      rw [← hyx]
      exact (hl' y).mp hy
    · intro hx
      refine ⟨l⁻¹ * x * l, ?_, ?_⟩
      · exact (hl' (l⁻¹ * x * l)).mpr
          (by rw [show l * (l⁻¹ * x * l) * l⁻¹ = x from by group]; exact hx)
      · rw [MulAut.smul_def, MulAut.conj_apply]
        group
  have hinv : ∀ g x : G, ‖χ (g * x * g⁻¹)‖ ^ 2 = ‖χ x‖ ^ 2 := by
    intro g x
    rw [ClassFunction.conj_eq χ x g]
  have hTI := OddOrder.GroupTheory.IsTISubset.sum_conjClassSet
    (A := Tset C.P.H0 C.P.U) (L := C.P.H) (M := ℝ) (f := fun x : G => ‖χ x‖ ^ 2)
    C.P.TI hstab hinv
  have hTI' : (∑ x ∈ TconjFin C, ‖χ x‖ ^ 2)
      = (C.P.H.index : ℝ) * ∑ x ∈ Tfin C, ‖χ x‖ ^ 2 := by
    simpa [TconjFin, Tfin, nsmul_eq_mul] using hTI
  -- the total sum
  have hsum : (∑ x : G, ‖χ x‖ ^ 2) = (Nat.card G : ℝ) := normSq_sum_univ χ hχ
  -- strictness: `1 ∉ T^G`, and `χ(1) ≠ 0`
  have hlt : (∑ x ∈ TconjFin C, ‖χ x‖ ^ 2) < ∑ x : G, ‖χ x‖ ^ 2 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset G)
      (fun x : G => x ∈ TconjFin C) (fun x : G => ‖χ x‖ ^ 2)
    have hfil : (Finset.univ.filter (fun x : G => x ∈ TconjFin C)) = TconjFin C := by
      ext x; simp
    rw [hfil] at hsplit
    have hpos : 0 < ∑ x ∈ (Finset.univ.filter (fun x : G => ¬ x ∈ TconjFin C)), ‖χ x‖ ^ 2 := by
      refine Finset.sum_pos' (fun x _ => by positivity) ⟨1, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, one_notMem_TconjFin C⟩
      · exact pow_pos (norm_pos_iff.mpr hχ.apply_one_ne_zero) 2
    linarith
  have hidxpos : (0 : ℝ) < (C.P.H.index : ℝ) := by
    have h : 0 < C.P.H.index := by
      rw [Subgroup.index_eq_card]; exact Nat.card_pos
    exact_mod_cast h
  have hcardH : Nat.card ↥C.P.H = 2 * Nat.card ↥C.P.H0 := by
    have h := Subgroup.relIndex_mul_card (H := C.P.H0) (K := C.P.H)
    rw [inf_eq_left.mpr C.P.H0_le_H, C.P.H0_relIndex] at h
    exact h.symm
  have hcard : (Nat.card G : ℝ) = (C.P.H.index : ℝ) * (2 * (Nat.card ↥C.P.H0 : ℝ)) := by
    have h1 : Nat.card ↥C.P.H * C.P.H.index = Nat.card G := Subgroup.card_mul_index _
    rw [← h1, hcardH]; push_cast; ring
  have htrans : (∑ x ∈ Tfin C, ‖χ x‖ ^ 2) = ∑ g ∈ TfinH C, ‖χ (g : G)‖ ^ 2 :=
    sum_Tfin_eq_sum_TfinH C (fun x : G => ‖χ x‖ ^ 2)
  have hmain : (C.P.H.index : ℝ) * (∑ g ∈ TfinH C, ‖χ (g : G)‖ ^ 2) < (Nat.card G : ℝ) := by
    rw [← htrans, ← hTI', ← hsum]
    exact hlt
  rw [hcard] at hmain
  have hfin := mul_lt_mul_of_pos_left hmain (inv_pos.mpr hidxpos)
  rwa [← mul_assoc, inv_mul_cancel₀ hidxpos.ne', one_mul, ← mul_assoc,
    inv_mul_cancel₀ hidxpos.ne', one_mul] at hfin

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **Bender–Glauberman 1981, Theorem 3.2**: `|𝒮(χ)| ≤ 3` for every `χ ∈ ±Irr(G)`. -/
theorem thm32 {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Thm32Prop D C := by
  intro hDC hS3 f hf χ hχ
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype ↥(Uin C) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(Uin C) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- the identity of Lemma 2.4 + Remark 3.1, in `ℂ`
  have hC := chi_sum_T_eq D C hDC f hf χ hχ
  -- `Ssum` is real
  have hSsum_real : Ssum C f χ = (((Ssum C f χ).re : ℝ) : ℂ) := by
    rw [Ssum, Complex.re_sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Ssum_term_ofReal C f hf χ hχ ν, Complex.ofReal_re]
  -- the same identity, in `ℝ`
  have hreal : (∑ g ∈ TfinH C, ‖χ (g : G)‖ ^ 2) =
      (Nat.card ↥C.P.H0 : ℝ) * (((bset C f χ).ncard : ℝ) - (Ssum C f χ).re) := by
    have hL : (∑ g ∈ TfinH C, χ (g : G) * star (χ (g : G))) =
        Complex.ofReal (∑ g ∈ TfinH C, ‖χ (g : G)‖ ^ 2) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Complex.star_def, ← Complex.normSq_eq_norm_sq]
      exact Complex.mul_conj (χ (g : G))
    have hR : (Nat.card ↥C.P.H0 : ℂ) * (((bset C f χ).ncard : ℂ) - Ssum C f χ) =
        Complex.ofReal ((Nat.card ↥C.P.H0 : ℝ) *
          (((bset C f χ).ncard : ℝ) - (Ssum C f χ).re)) := by
      rw [hSsum_real]
      rw [show ((((Ssum C f χ).re : ℝ) : ℂ)).re = (Ssum C f χ).re from
        Complex.ofReal_re ((Ssum C f χ).re)]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_sub,
        ← Complex.ofReal_mul]
    exact Complex.ofReal_inj.mp (hL.symm.trans (hC.trans hR))
  -- the two bounds
  have hbound := sum_TfinH_normSq_lt C χ hχ
  have hHpos : (0 : ℝ) < (Nat.card ↥C.P.H0 : ℝ) := by exact_mod_cast Nat.card_pos
  have hmain2 : (Nat.card ↥C.P.H0 : ℝ) * (((bset C f χ).ncard : ℝ) - (Ssum C f χ).re) <
      2 * (Nat.card ↥C.P.H0 : ℝ) := by
    rw [← hreal]
    exact hbound
  have hlt2 : ((bset C f χ).ncard : ℝ) - (Ssum C f χ).re < 2 := by
    rw [show ((bset C f χ).ncard : ℝ) - (Ssum C f χ).re =
        ((Nat.card ↥C.P.H0 : ℝ) * (((bset C f χ).ncard : ℝ) - (Ssum C f χ).re)) /
        (Nat.card ↥C.P.H0 : ℝ) from (mul_div_cancel_left₀ _ hHpos.ne').symm]
    exact (div_lt_iff₀ hHpos).mpr hmain2
  have hge : ((bset C f χ).ncard : ℝ) / 2 ≤
      ((bset C f χ).ncard : ℝ) - (Ssum C f χ).re := by
    have := two_re_Ssum_le D C hDC f hf χ hχ
    linarith
  have h4 : ((bset C f χ).ncard : ℝ) < 4 := by linarith
  have h4' : (bset C f χ).ncard < 4 := by exact_mod_cast h4
  omega

end Work.BG
