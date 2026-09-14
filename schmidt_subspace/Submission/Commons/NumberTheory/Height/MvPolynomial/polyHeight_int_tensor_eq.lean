import Mathlib
import Submission.Commons.NumberTheory.Height.MvPolynomial.polyHeight_mul_le

namespace Commons.NumberTheory.Height.MvPolynomial

open scoped BigOperators

variable {σ : Type*}

/-! ### Fintype-free variants of the `coeffSup` API -/

lemma bddAbove_range_coeff' (v : AbsoluteValue ℚ ℝ) (P : MvPolynomial σ ℚ) :
    BddAbove (Set.range fun m : σ →₀ ℕ => v (MvPolynomial.coeff m P)) := by
  classical
  refine ⟨Finset.sup' (insert 0 P.support) (Finset.insert_nonempty 0 _)
    ((fun p => v (MvPolynomial.coeff p P)) : (σ →₀ ℕ) → ℝ), ?_⟩
  rintro y ⟨m, rfl⟩
  by_cases hm : m ∈ P.support
  · exact Finset.le_sup' (fun p => v (MvPolynomial.coeff p P)) (Finset.mem_insert_of_mem hm)
  · change v (MvPolynomial.coeff m P) ≤ _
    rw [MvPolynomial.notMem_support_iff.mp hm, AbsoluteValue.map_zero]
    exact le_trans (v.nonneg _)
      (Finset.le_sup' (fun p => v (MvPolynomial.coeff p P)) (Finset.mem_insert_self 0 _))

/-- `coeffSup` evaluated at a coefficient. -/
lemma le_coeffSup' (v : AbsoluteValue ℚ ℝ) (P : MvPolynomial σ ℚ) (m : σ →₀ ℕ) :
    v (MvPolynomial.coeff m P) ≤ coeffSup v P :=
  le_ciSup (bddAbove_range_coeff' v P) m

lemma coeffSup_nonneg' (v : AbsoluteValue ℚ ℝ) (P : MvPolynomial σ ℚ) : 0 ≤ coeffSup v P :=
  Real.iSup_nonneg_of_nonnegHomClass v fun m => MvPolynomial.coeff m P

/-- The supremum defining `coeffSup` is attained. -/
lemma exists_coeffSup_eq (v : AbsoluteValue ℚ ℝ) (P : MvPolynomial σ ℚ) :
    ∃ m : σ →₀ ℕ, coeffSup v P = v (MvPolynomial.coeff m P) := by
  classical
  rcases P.support.eq_empty_or_nonempty with hemp | hne
  · have hcoeff : ∀ m, MvPolynomial.coeff m P = 0 := by
      intro m
      rw [← MvPolynomial.notMem_support_iff]
      rw [hemp]
      exact Finset.notMem_empty m
    refine ⟨0, ?_⟩
    rw [hcoeff 0, AbsoluteValue.map_zero]
    refine le_antisymm ?_ (coeffSup_nonneg' v P)
    refine ciSup_le fun m => ?_
    rw [hcoeff m, AbsoluteValue.map_zero]
  · obtain ⟨m₀, hm₀, hmax⟩ :=
      Finset.exists_max_image P.support (fun m => v (MvPolynomial.coeff m P)) hne
    refine ⟨m₀, ?_⟩
    refine le_antisymm ?_ (le_coeffSup' v P m₀)
    refine ciSup_le fun m => ?_
    by_cases hm : m ∈ P.support
    · exact hmax m hm
    · rw [MvPolynomial.notMem_support_iff.mp hm, AbsoluteValue.map_zero]
      exact v.nonneg _


/-! ### The coefficient formula for a tensor product of polynomials -/

lemma symm_sumFinsupp_eq_mapDomain_add {ι κ : Type*} (a : ι →₀ ℕ) (b : κ →₀ ℕ) :
    Finsupp.sumFinsuppEquivProdFinsupp.symm (a, b) =
      a.mapDomain Sum.inl + b.mapDomain Sum.inr := by
  ext x
  cases x with
  | inl y =>
    simp only [Finsupp.sumFinsuppEquivProdFinsupp_symm_inl, Finsupp.add_apply]
    rw [Finsupp.mapDomain_apply Sum.inl_injective]
    rw [Finsupp.mapDomain_of_notMem_range]
    simp
    intro h
    obtain ⟨z, hz⟩ := h
    exact Sum.inl_ne_inr hz.symm
  | inr y =>
    simp only [Finsupp.sumFinsuppEquivProdFinsupp_symm_inr, Finsupp.add_apply]
    rw [Finsupp.mapDomain_apply Sum.inr_injective]
    rw [Finsupp.mapDomain_of_notMem_range]
    simp
    intro h
    obtain ⟨z, hz⟩ := h
    exact Sum.inr_ne_inl hz.symm

lemma coeff_rename_mul_rename {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (P : MvPolynomial ι ℚ) (Q : MvPolynomial κ ℚ) (m : (ι ⊕ κ) →₀ ℕ) :
    MvPolynomial.coeff m (MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr Q)
      = MvPolynomial.coeff (Finsupp.sumFinsuppEquivProdFinsupp m).1 P *
        MvPolynomial.coeff (Finsupp.sumFinsuppEquivProdFinsupp m).2 Q := by
  classical
  set a : ι →₀ ℕ := (Finsupp.sumFinsuppEquivProdFinsupp m).1 with ha
  set b : κ →₀ ℕ := (Finsupp.sumFinsuppEquivProdFinsupp m).2 with hb
  have hm : a.mapDomain Sum.inl + b.mapDomain Sum.inr = m := by
    rw [← symm_sumFinsupp_eq_mapDomain_add a b]
    exact Equiv.symm_apply_apply _ m
  rw [MvPolynomial.coeff_mul]
  rw [Finset.sum_eq_single (a.mapDomain Sum.inl, b.mapDomain Sum.inr)]
  · simp only [MvPolynomial.coeff_rename_mapDomain _ Sum.inl_injective,
      MvPolynomial.coeff_rename_mapDomain _ Sum.inr_injective]
  · intro y hy hyne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hy
    by_cases h1 : MvPolynomial.coeff y.1 ((MvPolynomial.rename Sum.inl) P) = 0
    · rw [h1, zero_mul]
    · by_cases h2 : MvPolynomial.coeff y.2 ((MvPolynomial.rename Sum.inr) Q) = 0
      · rw [h2, mul_zero]
      · exfalso
        obtain ⟨d1, hd1, -⟩ := MvPolynomial.coeff_rename_ne_zero Sum.inl P y.1 h1
        obtain ⟨d2, hd2, -⟩ := MvPolynomial.coeff_rename_ne_zero Sum.inr Q y.2 h2
        have key : Finsupp.sumFinsuppEquivProdFinsupp (y.1 + y.2) = (d1, d2) := by
          rw [← hd1, ← hd2, ← symm_sumFinsupp_eq_mapDomain_add d1 d2]
          exact Equiv.apply_symm_apply _ (d1, d2)
        rw [hy] at key
        have hd1' : d1 = a := by rw [ha]; exact (congrArg Prod.fst key).symm
        have hd2' : d2 = b := by rw [hb]; exact (congrArg Prod.snd key).symm
        have hy1 : y.1 = a.mapDomain Sum.inl := by rw [← hd1, hd1']
        have hy2 : y.2 = b.mapDomain Sum.inr := by rw [← hd2, hd2']
        exact hyne (Prod.ext hy1 hy2)
  · intro hy
    exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; exact hm) hy

/-- Sup of a product of two nonnegative families is the product of the sups. -/
lemma ciSup_mul_ciSup_eq {α β : Type*} [Nonempty α] [Nonempty β] (f : α → ℝ) (g : β → ℝ)
    (hf : ∀ a, 0 ≤ f a) (hg : ∀ b, 0 ≤ g b) (hbf : BddAbove (Set.range f))
    (hbg : BddAbove (Set.range g)) :
    (⨆ a, f a) * (⨆ b, g b) = ⨆ p : α × β, f p.1 * g p.2 := by
  obtain ⟨M, hM⟩ := hbf
  obtain ⟨N, hN⟩ := hbg
  have hM' : ∀ a, f a ≤ M := fun a => hM (Set.mem_range_self a)
  have hN' : ∀ b, g b ≤ N := fun b => hN (Set.mem_range_self b)
  have hM0 : 0 ≤ M := le_trans (hf (Classical.arbitrary α)) (hM' _)
  have hbd : BddAbove (Set.range fun p : α × β => f p.1 * g p.2) :=
    ⟨M * N, by
      rintro _ ⟨p, rfl⟩
      exact mul_le_mul (hM' p.1) (hN' p.2) (hg p.2) (le_trans (hf p.1) (hM' p.1))⟩
  have hn : 0 ≤ (⨆ b, g b) := Real.iSup_nonneg hg
  rw [ciSup_prod hbd, Real.iSup_mul_of_nonneg hn]
  exact iSup_congr fun a => Real.mul_iSup_of_nonneg (hf a) g

/-- `coeffSup` is multiplicative for the tensor product of polynomials in disjoint variables. -/
lemma coeffSup_rename_mul_rename {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (v : AbsoluteValue ℚ ℝ) (P : MvPolynomial ι ℚ) (Q : MvPolynomial κ ℚ) :
    coeffSup v (MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr Q) =
      coeffSup v P * coeffSup v Q := by
  classical
  have key : coeffSup v (MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr Q)
      = ⨆ p : (ι →₀ ℕ) × (κ →₀ ℕ),
          v (MvPolynomial.coeff p.1 P) * v (MvPolynomial.coeff p.2 Q) := by
    rw [coeffSup]
    trans ⨆ m : (ι ⊕ κ) →₀ ℕ,
        v (MvPolynomial.coeff (Finsupp.sumFinsuppEquivProdFinsupp m).1 P) *
          v (MvPolynomial.coeff (Finsupp.sumFinsuppEquivProdFinsupp m).2 Q)
    · refine iSup_congr fun m => ?_
      rw [← map_mul, coeff_rename_mul_rename]
    · exact Equiv.iSup_comp (g := fun p : (ι →₀ ℕ) × (κ →₀ ℕ) =>
          v (MvPolynomial.coeff p.1 P) * v (MvPolynomial.coeff p.2 Q))
        Finsupp.sumFinsuppEquivProdFinsupp
  rw [key]
  rw [← ciSup_mul_ciSup_eq (f := fun a : ι →₀ ℕ => v (MvPolynomial.coeff a P))
        (g := fun b : κ →₀ ℕ => v (MvPolynomial.coeff b Q))
        (fun a => v.nonneg _) (fun b => v.nonneg _)
        (bddAbove_range_coeff' v P) (bddAbove_range_coeff' v Q)]
  rfl


/-! ### Sup over `Option` -/

lemma iSup_option_elim_eq {S : Type*} [Nonempty S] {a : ℝ} (f : S → ℝ)
    (hb : BddAbove (Set.range f)) :
    (⨆ o : Option S, o.elim a f) = max a (⨆ s : S, f s) := by
  have hbd : BddAbove (Set.range fun o : Option S => o.elim a f) :=
    ⟨max a (⨆ s, f s), by
      rintro _ ⟨o, rfl⟩
      cases o with
      | none => exact le_max_left _ _
      | some s => exact le_trans (le_ciSup hb s) (le_max_right _ _)⟩
  refine le_antisymm (ciSup_le fun o => ?_) (max_le ?_ ?_)
  · cases o with
    | none => exact le_max_left _ _
    | some s => exact le_trans (le_ciSup hb s) (le_max_right _ _)
  · exact le_ciSup hbd none
  · exact ciSup_le fun s => le_ciSup hbd (some s)

lemma gP_ne_zero' {σ : Type*} (P : MvPolynomial σ ℚ) : gP P ≠ 0 := by
  intro h
  have := congrFun h none
  simp [gP] at this

/-- The supremum of `v` over the tuple `gP P` (indexed by `Option`) is `max 1 (coeffSup v P)`. -/
lemma iSup_gP_eq' {σ : Type*} (v : AbsoluteValue ℚ ℝ) (P : MvPolynomial σ ℚ) :
    (⨆ o : Option (σ →₀ ℕ), v (gP P o)) = max 1 (coeffSup v P) := by
  have hfun : (fun o : Option (σ →₀ ℕ) => v (gP P o))
      = fun o => o.elim (v 1) (fun m => v (MvPolynomial.coeff m P)) := by
    funext o; cases o <;> simp [gP]
  rw [hfun, iSup_option_elim_eq (a := v 1) (fun m => v (MvPolynomial.coeff m P))
      (bddAbove_range_coeff' v P), AbsoluteValue.map_one]
  rfl

/-! ### The height of `gP (R.map cast)` for an integer polynomial -/

lemma one_le_coeffSup_intCast {σ : Type*} (v : NumberField.InfinitePlace ℚ)
    (R : MvPolynomial σ ℤ) (hR : R ≠ 0) :
    1 ≤ coeffSup v.val (R.map (Int.castRingHom ℚ)) := by
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hR
  rw [MvPolynomial.mem_support_iff] at hm
  have hcoeff : MvPolynomial.coeff m (R.map (Int.castRingHom ℚ))
      = ((MvPolynomial.coeff m R : ℤ) : ℚ) := MvPolynomial.coeff_map _ _ _
  have h1 : 1 ≤ v.val (((MvPolynomial.coeff m R : ℤ)) : ℚ) := by
    have h1' : 1 ≤ v (((MvPolynomial.coeff m R : ℤ)) : ℚ) := by
      rw [NumberField.InfinitePlace.map_intCast, Int.norm_eq_abs]
      exact_mod_cast Int.one_le_abs hm
    exact h1' 
  calc 1 ≤ v.val (MvPolynomial.coeff m (R.map (Int.castRingHom ℚ))) := by rwa [hcoeff]
    _ ≤ coeffSup v.val (R.map (Int.castRingHom ℚ)) := le_coeffSup' v.val _ m

lemma coeffSup_intCast_le_one {σ : Type*} (v : NumberField.FinitePlace ℚ)
    (R : MvPolynomial σ ℤ) :
    coeffSup v.val (R.map (Int.castRingHom ℚ)) ≤ 1 := by
  rw [coeffSup]
  refine ciSup_le fun m => ?_
  rw [MvPolynomial.coeff_map]
  exact IsNonarchimedean.apply_intCast_le_one (NumberField.FinitePlace.add_le v)

lemma mulHeight_gP_intCast {σ : Type*} (R : MvPolynomial σ ℤ) :
    Height.mulHeight (gP (R.map (Int.castRingHom ℚ))) =
      ∏ v : NumberField.InfinitePlace ℚ,
        (max 1 (coeffSup v.val (R.map (Int.castRingHom ℚ)))) ^ v.mult := by
  rw [NumberField.mulHeight_eq (gP_ne_zero' _)]
  have hfin : (∏ᶠ v : NumberField.FinitePlace ℚ,
        (⨆ i, v (gP (R.map (Int.castRingHom ℚ)) i))) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by
      change (⨆ o : Option (σ →₀ ℕ), v.val (gP (R.map (Int.castRingHom ℚ)) o)) = 1
      rw [iSup_gP_eq' v.val]
      exact max_eq_left (coeffSup_intCast_le_one v R)
  rw [hfin, mul_one]
  refine Finset.prod_congr rfl fun v _ => ?_
  change (⨆ o : Option (σ →₀ ℕ), v.val (gP (R.map (Int.castRingHom ℚ)) o)) ^ v.mult =
    max 1 (coeffSup v.val (R.map (Int.castRingHom ℚ))) ^ v.mult
  rw [iSup_gP_eq' v.val]

lemma mulHeight_gP_intCast_pos {σ : Type*} (R : MvPolynomial σ ℤ) :
    0 < Height.mulHeight (gP (R.map (Int.castRingHom ℚ))) := by
  rw [mulHeight_gP_intCast]
  exact Finset.prod_pos fun v _ =>
    pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) _


/-! ### The main theorem -/

lemma max_one_mul_of_ge_one {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    max 1 (a * b) = max 1 a * max 1 b := by
  have h : (1:ℝ) ≤ a * b := one_le_mul_of_one_le_of_one_le ha hb
  rw [max_eq_right h, max_eq_right ha, max_eq_right hb]

theorem polyHeight_int_tensor_eq {ι κ : Type*} (P : MvPolynomial ι ℤ) (Q : MvPolynomial κ ℤ)
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    Height.logHeight (fun o : Option ((ι ⊕ κ) →₀ ℕ) =>
      o.elim (1 : ℚ) (fun m => MvPolynomial.coeff m
        ((MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr Q).map
          (Int.castRingHom ℚ)))) =
    Height.logHeight (fun o : Option (ι →₀ ℕ) =>
      o.elim (1 : ℚ) (fun m => MvPolynomial.coeff m (P.map (Int.castRingHom ℚ)))) +
    Height.logHeight (fun o : Option (κ →₀ ℕ) =>
      o.elim (1 : ℚ) (fun m => MvPolynomial.coeff m (Q.map (Int.castRingHom ℚ)))) := by
  classical
  have hT : (MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr Q).map (Int.castRingHom ℚ)
      = MvPolynomial.rename Sum.inl (P.map (Int.castRingHom ℚ)) *
        MvPolynomial.rename Sum.inr (Q.map (Int.castRingHom ℚ)) := by
    simp only [map_mul, MvPolynomial.map_rename]
  have key : Height.mulHeight (gP ((MvPolynomial.rename Sum.inl P *
        MvPolynomial.rename Sum.inr Q).map (Int.castRingHom ℚ)))
      = Height.mulHeight (gP (P.map (Int.castRingHom ℚ))) *
        Height.mulHeight (gP (Q.map (Int.castRingHom ℚ))) := by
    rw [mulHeight_gP_intCast (MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr Q),
      mulHeight_gP_intCast P, mulHeight_gP_intCast Q, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← mul_pow]
    congr 1
    rw [hT, coeffSup_rename_mul_rename]
    exact max_one_mul_of_ge_one (one_le_coeffSup_intCast v P hP) (one_le_coeffSup_intCast v Q hQ)
  change Height.logHeight (gP ((MvPolynomial.rename Sum.inl P *
      MvPolynomial.rename Sum.inr Q).map (Int.castRingHom ℚ))) =
    Height.logHeight (gP (P.map (Int.castRingHom ℚ))) +
    Height.logHeight (gP (Q.map (Int.castRingHom ℚ)))
  rw [Height.logHeight_eq_log_mulHeight, Height.logHeight_eq_log_mulHeight,
    Height.logHeight_eq_log_mulHeight, key,
    Real.log_mul (ne_of_gt (mulHeight_gP_intCast_pos P)) (ne_of_gt (mulHeight_gP_intCast_pos Q))]

end Commons.NumberTheory.Height.MvPolynomial
