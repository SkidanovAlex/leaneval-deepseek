import Mathlib
import Submission.Work.BW.Est17Ext

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false

namespace Work.BW

open Complex

variable {K : Type*} [Field K] [NumberField K] {r : ℕ}

/-! ## The `2^r · [K : ℚ]` family spanning `ℚ(φ(K), ρ)`

`EL φ ρ` is the subfield `ℚ(φ(K), ρ₁,…,ρ_r) ⊆ ℂ`.  For `kᵢ` a `ℚ`-basis of `K` and
`ε : Fin r → Fin 2` we consider the complex numbers `φ(kᵢ)·∏ⱼ ρⱼ^{εⱼ}`.  They span `EL φ ρ` over
`ℚ` (because `ksp φ ρ`, the set of `φ(K)`-linear combinations of the `2^r` products `∏ⱼ ρⱼ^{εⱼ}`,
equals both `EL φ ρ` and the `ℚ`-span of this family), and under the Kummer condition they are
`ℚ`-linearly independent (`kummer_indep`).  Hence they form a `ℚ`-basis and
`[EL φ ρ : ℚ] = 2^r · [K : ℚ]`. -/

/-- The family of `2^r · [K : ℚ]` complex numbers `φ(kᵢ)·∏ⱼ ρⱼ^{εⱼ}`. -/
noncomputable def bwVec (φ : K →+* ℂ) (ρ : Fin r → ℂ) :
    Fin (Module.finrank ℚ K) × (Fin r → Fin 2) → ℂ :=
  fun p => φ (kbasis K p.1) * ∏ j, ρ j ^ (p.2 j : ℕ)

@[simp] theorem bwVec_apply (φ : K →+* ℂ) (ρ : Fin r → ℂ)
    (p : Fin (Module.finrank ℚ K) × (Fin r → Fin 2)) :
    bwVec φ ρ p = φ (kbasis K p.1) * ∏ j, ρ j ^ (p.2 j : ℕ) := rfl

/-- `algebraMap ℚ A q = (q : A)`. -/
theorem algebraMap_ratCast_eq (A : Type*) [DivisionRing A] [Algebra ℚ A] (q : ℚ) :
    algebraMap ℚ A q = (q : A) := by
  simpa using (algebraMap.coe_ratCast ℚ A q)

/-- `φ (algebraMap ℚ K q) = (q : ℂ)`. -/
theorem phi_algebraMap_rat (φ : K →+* ℂ) (q : ℚ) :
    φ (algebraMap ℚ K q) = (q : ℂ) := by
  rw [algebraMap_ratCast_eq K q]
  exact map_ratCast φ q

/-! ### `ksp` and its elementary members -/

/-- `ksp φ ρ` is the range of `Tfun φ ρ`. -/
theorem mem_ksp_iff {φ : K →+* ℂ} {ρ : Fin r → ℂ} {x : ℂ} :
    x ∈ ksp φ ρ ↔ ∃ c : (Fin r → Fin 2) → K, Tfun φ ρ c = x := by
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩

theorem zero_mem_ksp (φ : K →+* ℂ) (ρ : Fin r → ℂ) : (0 : ℂ) ∈ ksp φ ρ :=
  mem_ksp_iff.mpr ⟨0, Tfun_zero φ ρ⟩

theorem one_mem_ksp (φ : K →+* ℂ) (ρ : Fin r → ℂ) : (1 : ℂ) ∈ ksp φ ρ :=
  mem_ksp_iff.mpr ⟨fun ε => if ε = 0 then (1 : K) else 0, by
    rw [Tfun_single φ ρ (1 : K), map_one]⟩

theorem add_mem_ksp (φ : K →+* ℂ) (ρ : Fin r → ℂ) {x y : ℂ}
    (hx : x ∈ ksp φ ρ) (hy : y ∈ ksp φ ρ) : x + y ∈ ksp φ ρ := by
  obtain ⟨c, rfl⟩ := mem_ksp_iff.mp hx
  obtain ⟨d, rfl⟩ := mem_ksp_iff.mp hy
  exact mem_ksp_iff.mpr ⟨c + d, Tfun_add φ ρ c d⟩

theorem neg_mem_ksp (φ : K →+* ℂ) (ρ : Fin r → ℂ) {x : ℂ} (hx : x ∈ ksp φ ρ) :
    -x ∈ ksp φ ρ := by
  obtain ⟨c, rfl⟩ := mem_ksp_iff.mp hx
  exact mem_ksp_iff.mpr ⟨-c, Tfun_neg φ ρ c⟩

theorem rat_mem_ksp (φ : K →+* ℂ) (ρ : Fin r → ℂ) (q : ℚ) : (q : ℂ) ∈ ksp φ ρ :=
  mem_ksp_iff.mpr ⟨fun ε => if ε = 0 then (q : K) else 0, by
    rw [Tfun_single φ ρ (q : K), map_ratCast]⟩

theorem phi_mem_ksp (φ : K →+* ℂ) (ρ : Fin r → ℂ) (a : K) : φ a ∈ ksp φ ρ :=
  mem_ksp_iff.mpr ⟨fun ε => if ε = 0 then a else 0, Tfun_single φ ρ a⟩

theorem mul_mem_ksp (φ : K →+* ℂ) (η : Fin r → K) (ρ : Fin r → ℂ)
    (hρ : ∀ j, ρ j ^ 2 = φ (η j)) {x y : ℂ} (hx : x ∈ ksp φ ρ) (hy : y ∈ ksp φ ρ) :
    x * y ∈ ksp φ ρ :=
  ksp_mul φ η ρ hρ hx hy

/-! ### `Bfun` and `ρ_j` in `ksp` -/

theorem Bfun_single (ρ : Fin r → ℂ) (j : Fin r) :
    Bfun ρ (Pi.single j (1 : Fin 2)) = ρ j := by
  rw [Bfun, Finset.prod_eq_single j]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb]
    simp
  · intro h; exact absurd (Finset.mem_univ j) h

theorem Bfun_mem_ksp (φ : K →+* ℂ) (ρ : Fin r → ℂ) (ε : Fin r → Fin 2) :
    Bfun ρ ε ∈ ksp φ ρ := by
  refine mem_ksp_iff.mpr ⟨fun δ => if δ = ε then (1 : K) else 0, ?_⟩
  rw [Tfun_eq_single φ ρ _ ε (fun δ hδ => if_neg hδ)]
  simp

theorem rho_mem_ksp (φ : K →+* ℂ) (ρ : Fin r → ℂ) (j : Fin r) : ρ j ∈ ksp φ ρ := by
  refine mem_ksp_iff.mpr ⟨fun δ => if δ = Pi.single j (1 : Fin 2) then (1 : K) else 0, ?_⟩
  rw [Tfun_eq_single φ ρ _ (Pi.single j (1 : Fin 2)) (fun δ hδ => if_neg hδ)]
  simp [Bfun_single]

/-! ### `ksp ⊆ EL` -/

theorem ksp_subset_EL (φ : K →+* ℂ) (ρ : Fin r → ℂ) {x : ℂ} (hx : x ∈ ksp φ ρ) :
    x ∈ (EL φ ρ : Set ℂ) := by
  obtain ⟨c, rfl⟩ := mem_ksp_iff.mp hx
  simp only [Tfun, Bfun]
  refine (EL φ ρ).toSubfield.sum_mem (fun ε _ => ?_)
  refine (EL φ ρ).toSubfield.mul_mem (by simpa using (inclE φ ρ (c ε)).2) ?_
  refine (EL φ ρ).toSubfield.prod_mem (fun i _ => ?_)
  exact pow_mem (by simpa using (rhoE φ ρ i).2) (ε i : ℕ)

/-! ### `EL ⊆ ksp` -/

theorem EL_subset_ksp (φ : K →+* ℂ) (η : Fin r → K) (ρ : Fin r → ℂ)
    (hρ : ∀ j, ρ j ^ 2 = φ (η j)) {x : ℂ} (hx : x ∈ (EL φ ρ : Set ℂ)) :
    x ∈ ksp φ ρ := by
  have hx' : x ∈ Subfield.closure (Set.range (algebraMap ℚ ℂ) ∪
      (Set.range (fun i => φ (kbasis K i)) ∪ Set.range ρ)) := by
    have h1 : x ∈ (IntermediateField.adjoin ℚ
        (Set.range (fun i => φ (kbasis K i)) ∪ Set.range ρ) : Set ℂ) := hx
    rw [← IntermediateField.coe_toSubfield] at h1
    rw [IntermediateField.adjoin_toSubfield] at h1
    exact h1
  exact Subfield.closure_induction (p := fun x _ => x ∈ ksp φ ρ)
    (fun y hy => by
      rcases hy with hy | hy
      · obtain ⟨q, rfl⟩ := hy
        rw [algebraMap_ratCast_eq ℂ q]
        exact rat_mem_ksp φ ρ q
      · rcases hy with hy | hy
        · obtain ⟨i, rfl⟩ := hy; exact phi_mem_ksp φ ρ (kbasis K i)
        · obtain ⟨j, rfl⟩ := hy; exact rho_mem_ksp φ ρ j)
    (one_mem_ksp φ ρ)
    (fun y z _ _ hy hz => add_mem_ksp φ ρ hy hz)
    (fun y _ hy => neg_mem_ksp φ ρ hy)
    (fun y _ hy => by
      by_cases h : y = 0
      · rw [h, inv_zero]; exact zero_mem_ksp φ ρ
      · exact ksp_inv φ η ρ hρ hy h)
    (fun y z _ _ hy hz => mul_mem_ksp φ η ρ hρ hy hz)
    hx'

/-! ### `ksp ⊆ span` -/

theorem ksp_subset_span (φ : K →+* ℂ) (ρ : Fin r → ℂ) {x : ℂ} (hx : x ∈ ksp φ ρ) :
    x ∈ Submodule.span ℚ (Set.range (bwVec φ ρ)) := by
  obtain ⟨c, rfl⟩ := mem_ksp_iff.mp hx
  simp only [Tfun]
  have hrepr : ∀ ε : Fin r → Fin 2, φ (c ε)
      = ∑ i, ((kbasis K).repr (c ε) i : ℂ) * φ (kbasis K i) := by
    intro ε
    conv_lhs => rw [← (kbasis K).sum_repr (c ε)]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Algebra.smul_def, map_mul, phi_algebraMap_rat φ]
  have hε : (∑ ε : Fin r → Fin 2, φ (c ε) * Bfun ρ ε)
      = ∑ ε : Fin r → Fin 2, ∑ i, ((kbasis K).repr (c ε) i) • bwVec φ ρ (i, ε) := by
    apply Finset.sum_congr rfl
    intro ε _
    rw [hrepr ε, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [bwVec_apply, Bfun, Algebra.smul_def, algebraMap_ratCast_eq ℂ]
    ring
  have hpair : (∑ ε : Fin r → Fin 2, ∑ i, ((kbasis K).repr (c ε) i) • bwVec φ ρ (i, ε))
      = ∑ p : Fin (Module.finrank ℚ K) × (Fin r → Fin 2),
          ((kbasis K).repr (c p.2) p.1) • bwVec φ ρ p :=
    (Fintype.sum_prod_type_right (f := fun p : Fin (Module.finrank ℚ K) × (Fin r → Fin 2) =>
      ((kbasis K).repr (c p.2) p.1) • bwVec φ ρ p)).symm
  rw [hε, hpair]
  exact Submodule.sum_mem _ (fun p _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self p)))

/-! ### Linear independence of the family -/

theorem linIndep_bwVec (φ : K →+* ℂ) (η : Fin r → K) (hη : ∀ j, η j ≠ 0)
    (hK : KummerCond η) (ρ : Fin r → ℂ) (hρ : ∀ j, ρ j ^ 2 = φ (η j)) :
    LinearIndependent ℚ (bwVec φ ρ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsum : ∑ ε : Fin r → Fin 2,
      φ (∑ i, g (i, ε) • kbasis K i) * ∏ j, ρ j ^ (ε j : ℕ) = 0 := by
    have h1 : ∀ ε : Fin r → Fin 2,
        (∑ i, g (i, ε) • bwVec φ ρ (i, ε))
          = φ (∑ i, g (i, ε) • kbasis K i) * ∏ j, ρ j ^ (ε j : ℕ) := by
      intro ε
      have h2 : ∀ i, g (i, ε) • bwVec φ ρ (i, ε)
          = ((g (i, ε) : ℂ) * φ (kbasis K i)) * ∏ j, ρ j ^ (ε j : ℕ) := by
        intro i
        simp only [bwVec_apply, Bfun, Algebra.smul_def, algebraMap_ratCast_eq ℂ]
        ring
      rw [Finset.sum_congr rfl (fun i _ => h2 i), ← Finset.sum_mul]
      congr 1
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Algebra.smul_def, map_mul, phi_algebraMap_rat φ]
    calc ∑ ε : Fin r → Fin 2, φ (∑ i, g (i, ε) • kbasis K i) * ∏ j, ρ j ^ (ε j : ℕ)
        = ∑ ε : Fin r → Fin 2, ∑ i, g (i, ε) • bwVec φ ρ (i, ε) := by
          apply Finset.sum_congr rfl; intro ε _; rw [h1 ε]
      _ = ∑ p : Fin (Module.finrank ℚ K) × (Fin r → Fin 2), g p • bwVec φ ρ p :=
          (Fintype.sum_prod_type_right (f := fun p : Fin (Module.finrank ℚ K) × (Fin r → Fin 2) =>
            g p • bwVec φ ρ p)).symm
      _ = 0 := hg
  have ha := kummer_indep φ η hη hK ρ hρ (fun ε => ∑ i, g (i, ε) • kbasis K i) hsum
  intro p
  obtain ⟨i, ε⟩ := p
  have h0 : ∑ i', g (i', ε) • kbasis K i' = 0 := congrFun ha ε
  exact Fintype.linearIndependent_iff.mp (kbasis K).linearIndependent (fun i' => g (i', ε)) h0 i

/-! ### The degree of the Kummer extension -/

/-- The degree of the Kummer extension: `[ℚ(φ(K), ρ₁,…,ρ_r) : ℚ] = 2^r · [K : ℚ]`
when `ρ_j² = φ(η_j)` and the `η_j` satisfy the Kummer condition. -/
theorem est17_finrank {K : Type*} [Field K] [NumberField K] {r : ℕ} {φ : K →+* ℂ}
    {ρ : Fin r → ℂ} {η : Fin r → K} (hη : ∀ j, η j ≠ 0)
    (hρ : ∀ j, ρ j ^ 2 = φ (η j)) (hK : KummerCond η) :
    Module.finrank ℚ (EL φ ρ) = 2 ^ r * Module.finrank ℚ K := by
  have hli := linIndep_bwVec φ η hη hK ρ hρ
  have hgen : Set.range (bwVec φ ρ) ⊆ ksp φ ρ := by
    rintro y ⟨p, rfl⟩
    rw [bwVec_apply]
    exact mul_mem_ksp φ η ρ hρ (phi_mem_ksp φ ρ (kbasis K p.1))
      (by simpa only [Bfun] using Bfun_mem_ksp φ ρ p.2)
  have hS_sub : ∀ x ∈ (Submodule.span ℚ (Set.range (bwVec φ ρ)) : Set ℂ),
      x ∈ ksp φ ρ := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => x ∈ ksp φ ρ) (fun y hy => hgen hy)
      (zero_mem_ksp φ ρ) (fun y z _ _ hy hz => add_mem_ksp φ ρ hy hz) (fun a y _ hy => ?_) hx
    rw [Algebra.smul_def, algebraMap_ratCast_eq ℂ]
    exact mul_mem_ksp φ η ρ hρ (rat_mem_ksp φ ρ a) hy
  have hS_sub_EL : ∀ x ∈ (Submodule.span ℚ (Set.range (bwVec φ ρ)) : Set ℂ),
      x ∈ (EL φ ρ : Set ℂ) :=
    fun x hx => ksp_subset_EL φ ρ (hS_sub x hx)
  have hEL_sub_S : ∀ x ∈ (EL φ ρ : Set ℂ),
      x ∈ (Submodule.span ℚ (Set.range (bwVec φ ρ)) : Set ℂ) :=
    fun x hx => ksp_subset_span φ ρ (EL_subset_ksp φ η ρ hρ hx)
  have hS_eq : Submodule.span ℚ (Set.range (bwVec φ ρ)) = (EL φ ρ).toSubalgebra.toSubmodule := by
    ext x
    change x ∈ (Submodule.span ℚ (Set.range (bwVec φ ρ)) : Set ℂ) ↔ x ∈ ((EL φ ρ) : Set ℂ)
    exact ⟨fun hx => hS_sub_EL x hx, fun hx => hEL_sub_S x hx⟩
  calc Module.finrank ℚ (EL φ ρ)
      = Module.finrank ℚ ((EL φ ρ).toSubalgebra) :=
        (IntermediateField.finrank_eq_finrank_subalgebra _).symm
    _ = Module.finrank ℚ ((EL φ ρ).toSubalgebra.toSubmodule) :=
        (Subalgebra.finrank_toSubmodule _).symm
    _ = Module.finrank ℚ (Submodule.span ℚ (Set.range (bwVec φ ρ))) := by rw [← hS_eq]
    _ = Fintype.card (Fin (Module.finrank ℚ K) × (Fin r → Fin 2)) := finrank_span_eq_card hli
    _ = Module.finrank ℚ K * 2 ^ r := by
        rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          Fintype.card_fin]
    _ = 2 ^ r * Module.finrank ℚ K := by rw [mul_comm]

end Work.BW
