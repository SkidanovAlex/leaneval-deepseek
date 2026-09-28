import Mathlib
import Submission.Work.HP.Q44Child.SuperDefs
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.Q44Child.SuperGram
import Submission.Work.HP.Q44Child.Gamma_span_indep
import Submission.Work.HP.Q44Child.covolume_eq_gram_det

/-!
# Auxiliary lemmas for `Work.HP.Q44Child.superlattice_count`

Structural facts about `Lℝ Λ`, `W Λ`, `ΓW Λ` and `Ggen`.
-/

namespace Work.HP.Q44Child

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

noncomputable section

open scoped RealInnerProductSpace
open Module

/-- The two-element family `b 0, b 1`. -/
def pair (b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)) : Fin 2 → (Fin 5 → ℤ) :=
  fun i => b (Fin.castLE (by norm_num : 2 ≤ 5) i)

lemma pair_injective (b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)) : Function.Injective (pair b) := by
  intro i j hij
  have h : Fin.castLE (by norm_num : 2 ≤ 5) i = Fin.castLE (by norm_num : 2 ≤ 5) j :=
    b.injective hij
  exact Fin.castLE_injective _ h

lemma pair_linIndep {b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)}
    (hli : LinearIndependent ℝ (fun i : Fin 5 => toE (b i))) :
    LinearIndependent ℝ (fun i : Fin 2 => toE (pair b i)) := by
  simpa [pair, Function.comp_def] using
    hli.comp (Fin.castLE (by norm_num : 2 ≤ 5)) (Fin.castLE_injective _)

section Structural

variable {Λ : Submodule ℤ (Fin 5 → ℤ)}
variable {b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)}

/-- `Lℝ Λ` is the real span of `toE (b 0), toE (b 1)`. -/
lemma Lℝ_eq_of_basis (hb : Λ = Submodule.span ℤ (Set.range (pair b))) :
    Lℝ Λ = Submodule.span ℝ (Set.range fun i : Fin 2 => toE (pair b i)) := by
  have h1 : ΛE Λ = Submodule.span ℤ (Set.range fun i : Fin 2 => toE (pair b i)) := by
    rw [ΛE, hb, Submodule.map_span, ← Set.range_comp]
    rfl
  rw [Lℝ, h1, Submodule.span_span_of_tower ℤ]

lemma finrank_Lℝ (hb : Λ = Submodule.span ℤ (Set.range (pair b)))
    (hli : LinearIndependent ℝ (fun i : Fin 5 => toE (b i))) :
    Module.finrank ℝ (Lℝ Λ) = 2 := by
  rw [Lℝ_eq_of_basis hb, finrank_span_eq_card (pair_linIndep hli)]
  simp

lemma finrank_E5 : Module.finrank ℝ E5 = 5 := by
  simp [E5]

lemma finrank_W (hb : Λ = Submodule.span ℤ (Set.range (pair b)))
    (hli : LinearIndependent ℝ (fun i : Fin 5 => toE (b i))) :
    Module.finrank ℝ (W Λ) = 3 := by
  have h := Submodule.finrank_add_finrank_orthogonal (Lℝ Λ)
  rw [finrank_Lℝ hb hli, finrank_E5] at h
  rw [W]
  omega

end Structural

section Gamma

variable {Λ : Submodule ℤ (Fin 5 → ℤ)}

/-- The `ℤ`-linear map `m ↦ π (toE m)` with values in `W Λ`. -/
def Ψ (Λ : Submodule ℤ (Fin 5 → ℤ)) : (Fin 5 → ℤ) →ₗ[ℤ] W Λ where
  toFun m := ⟨proj Λ (toE m), proj_mem Λ _⟩
  map_add' m n := by
    ext i
    show (proj Λ (toE (m + n)) : E5) i
      = ((⟨proj Λ (toE m), proj_mem Λ _⟩ + ⟨proj Λ (toE n), proj_mem Λ _⟩ : W Λ) : E5) i
    rw [toE_add, map_add]
    rfl
  map_smul' c m := by
    ext i
    show (proj Λ (toE (c • m)) : E5) i
      = ((c • (⟨proj Λ (toE m), proj_mem Λ _⟩ : W Λ)) : E5) i
    rw [toE_smul, map_zsmul]

@[simp] lemma Ψ_apply (Λ : Submodule ℤ (Fin 5 → ℤ)) (m : Fin 5 → ℤ) :
    Ψ Λ m = ⟨proj Λ (toE m), proj_mem Λ _⟩ := rfl


lemma ΓW_eq_map : ΓW Λ = Submodule.map (Ψ Λ) ⊤ := by
  rw [ΓW, span_stdBasis_eq_top, Submodule.map_span, ← Set.range_comp]
  congr 1

lemma Ψ_mem_ΓW (m : Fin 5 → ℤ) : Ψ Λ m ∈ ΓW Λ := by
  rw [ΓW_eq_map]
  exact Submodule.mem_map_of_mem Submodule.mem_top

/-- Every point of `W Λ` is within `√5/2` of a point of `ΓW Λ`. -/
lemma exists_close_ΓW (x : W Λ) : ∃ u ∈ ΓW Λ, ‖x - u‖ ≤ Real.sqrt 5 / 2 := by
  obtain ⟨m, hm⟩ := exists_int_close (x : E5)
  refine ⟨Ψ Λ m, Ψ_mem_ΓW m, ?_⟩
  have hx : proj Λ (x : E5) = (x : E5) :=
    (proj_eq_self_iff Λ _).mpr x.2
  rw [← Submodule.norm_coe (x - Ψ Λ m), Submodule.coe_sub]
  show ‖(x : E5) - proj Λ (toE m)‖ ≤ Real.sqrt 5 / 2
  rw [← hx, ← map_sub]
  exact le_trans (norm_proj_le Λ _) hm

end Gamma


section Det

variable {Λ : Submodule ℤ (Fin 5 → ℤ)}
variable {b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)}

/-- The two-element `ℤ`-basis `b 0, b 1` of `Λ`. -/
noncomputable def pairBasis (b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ))
    (Λ : Submodule ℤ (Fin 5 → ℤ)) (hb : Λ = Submodule.span ℤ (Set.range (pair b))) :
    Basis (Fin 2) ℤ Λ :=
  Basis.mk (v := fun i => (⟨pair b i, by rw [hb]; exact Submodule.subset_span ⟨i, rfl⟩⟩ : Λ))
    (LinearIndependent.of_comp (Submodule.subtype Λ) (by
      simpa [pair, Function.comp_def] using
        (b.linearIndependent.comp (Fin.castLE (by norm_num : 2 ≤ 5))
          (Fin.castLE_injective _))))
    (by
      intro x _
      have hmap : Submodule.map (Submodule.subtype Λ)
          (Submodule.span ℤ (Set.range fun i => (⟨pair b i,
            by rw [hb]; exact Submodule.subset_span ⟨i, rfl⟩⟩ : Λ)))
          = Submodule.span ℤ (Set.range (pair b)) := by
        rw [Submodule.map_span]
        congr 1
        rw [← Set.range_comp]
        rfl
      have hx : (x : Fin 5 → ℤ) ∈ Submodule.map (Submodule.subtype Λ)
          (Submodule.span ℤ (Set.range fun i => (⟨pair b i,
            by rw [hb]; exact Submodule.subset_span ⟨i, rfl⟩⟩ : Λ))) := by
        rw [hmap, ← hb]
        exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := Subtype.ext hyx
      simpa [this] using hy)

@[simp] lemma pairBasis_apply (hb : Λ = Submodule.span ℤ (Set.range (pair b))) (i : Fin 2) :
    ((pairBasis b Λ hb i : Λ) : Fin 5 → ℤ) = pair b i := by
  unfold pairBasis
  exact congrArg Subtype.val (Module.Basis.mk_apply (R := ℤ) (M := Λ)
    (v := fun i => (⟨pair b i, by rw [hb]; exact Submodule.subset_span ⟨i, rfl⟩⟩ : Λ)) _ _ i)

/-- `detL Λ` is the square root of the Gram determinant of the pair `b 0, b 1`. -/
lemma detL_eq_sqrt_gram_pair (hb : Λ = Submodule.span ℤ (Set.range (pair b))) :
    detL Λ = Real.sqrt ((Matrix.gram ℝ (fun i : Fin 2 => toE (pair b i))).det) := by
  rw [Work.HP.Lat.detL_basis_gram Λ (pairBasis b Λ hb)]
  congr 1
  congr 1
  ext i j
  rw [Matrix.gram_apply]
  simp [pairBasis_apply hb, inner_toE]

lemma detL_pos (hb : Λ = Submodule.span ℤ (Set.range (pair b)))
    (hli : LinearIndependent ℝ (fun i : Fin 5 => toE (b i))) : 0 < detL Λ := by
  rw [detL_eq_sqrt_gram_pair hb]
  refine Real.sqrt_pos.mpr (lt_of_le_of_ne' (Matrix.posSemidef_gram ℝ
    (fun i : Fin 2 => toE (pair b i))).det_nonneg ?_)
  exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr (pair_linIndep hli)

lemma det_gram_pair_eq (hb : Λ = Submodule.span ℤ (Set.range (pair b)))
    (hli : LinearIndependent ℝ (fun i : Fin 5 => toE (b i))) :
    (Matrix.gram ℝ (fun i : Fin 2 => toE (pair b i))).det = detL Λ ^ 2 := by
  rw [detL_eq_sqrt_gram_pair hb, Real.sq_sqrt]
  exact (Matrix.posSemidef_gram ℝ (fun i : Fin 2 => toE (pair b i))).det_nonneg

end Det

section Covol

variable {Λ : Submodule ℤ (Fin 5 → ℤ)}
variable {b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)}

/-- Every `π (toE m)`, `m ∈ ℤ^5`, lies in the `ℝ`-span of the generators `π (toE e_i)`. -/
lemma proj_toE_mem_span (m : Fin 5 → ℤ) :
    proj Λ (toE m) ∈ Submodule.span ℝ (Set.range fun i : Fin 5 => proj Λ (toE (Pi.single i 1))) := by
  have hm : m ∈ Submodule.span ℤ (Set.range fun i : Fin 5 => Pi.single i (1 : ℤ)) := by
    rw [← span_stdBasis_eq_top]; exact Submodule.mem_top
  refine Submodule.span_induction (p := fun x _ => proj Λ (toE x) ∈
    Submodule.span ℝ (Set.range fun i : Fin 5 => proj Λ (toE (Pi.single i 1))))
    ?_ ?_ ?_ ?_ hm
  · rintro x ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  · simp
  · intro x y _ _ hx hy
    rw [toE_add, map_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [toE_smul, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ c]
    exact Submodule.smul_mem _ _ hx

/-- The `ℝ`-span of all `π (toE m)` is `W Λ`. -/
lemma span_range_proj_toE_eq (Λ : Submodule ℤ (Fin 5 → ℤ)) :
    Submodule.span ℝ (Set.range fun m : Fin 5 → ℤ => proj Λ (toE m)) = W Λ := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro x ⟨m, rfl⟩
    exact proj_mem Λ _
  · intro y hy
    rw [← (proj_eq_self_iff Λ y).mpr hy]
    have hmem : (y : E5) ∈ Submodule.span ℝ (Set.range toE) := by
      rw [span_range_toE_eq_top]
      exact Submodule.mem_top
    have h2 : proj Λ (y : E5) ∈ Submodule.map (proj Λ).toLinearMap (Submodule.span ℝ (Set.range toE)) :=
      Submodule.mem_map_of_mem (f := (proj Λ).toLinearMap) hmem
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro x ⟨z, ⟨m, rfl⟩, rfl⟩
    exact ⟨m, rfl⟩

/-- The real span of `ΓW Λ` is all of `W Λ`. -/
lemma span_ℝ_ΓW_eq_top : Submodule.span ℝ (ΓW Λ : Set (W Λ)) = ⊤ := by
  have hgen : Submodule.map (LinearMap.restrictScalars ℤ (Submodule.subtype (W Λ))) (ΓW Λ)
      = Submodule.span ℤ (Set.range fun i : Fin 5 => proj Λ (toE (Pi.single i 1))) := by
    rw [ΓW, Submodule.map_span, ← Set.range_comp]
    rfl
  have hcoe : ((Submodule.map (LinearMap.restrictScalars ℤ (Submodule.subtype (W Λ)))
      (ΓW Λ) : Set E5)) = (Submodule.subtype (W Λ)) '' ↑(ΓW Λ) := by
    rw [Submodule.map_coe]
    rfl
  have hmap : Submodule.map (Submodule.subtype (W Λ))
      (Submodule.span ℝ (ΓW Λ : Set (W Λ))) = W Λ := by
    rw [Submodule.map_span, ← hcoe, hgen, Submodule.span_span_of_tower ℤ]
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      exact proj_mem Λ _
    · rw [← span_range_proj_toE_eq Λ]
      rw [Submodule.span_le]
      rintro x ⟨m, rfl⟩
      exact proj_toE_mem_span m
  rw [eq_top_iff]
  intro y _
  have h2 : (y : E5) ∈ Submodule.map (Submodule.subtype (W Λ))
      (Submodule.span ℝ (ΓW Λ : Set (W Λ))) := by rw [hmap]; exact y.2
  obtain ⟨z, hz, hzy⟩ := h2
  have : z = y := Subtype.ext hzy
  simpa [this] using hz

end Covol

section Covolume

variable {Λ : Submodule ℤ (Fin 5 → ℤ)}
variable {b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)}

lemma finSumFinEquiv_inl (a : Fin 2) :
    finSumFinEquiv (m := 2) (n := 3) (Sum.inl a) =
      (Fin.castLE (by norm_num : 2 ≤ 5) a : Fin 5) :=
  Fin.ext (by rw [finSumFinEquiv_apply_left (m := 2) (n := 3) a]; rfl)

lemma finSumFinEquiv_inr (j : Fin 3) :
    finSumFinEquiv (m := 2) (n := 3) (Sum.inr j) = idx3 j :=
  Fin.ext (by
    rw [finSumFinEquiv_apply_right (m := 2) (n := 3) j]
    simp [Fin.natAdd, idx3, Nat.add_comm])

lemma gram_sumElim_eq (b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)) :
    Matrix.gram ℝ (fun i : Sum (Fin 2) (Fin 3) =>
        Sum.elim (fun i => toE (pair b i)) (fun j => toE (b (idx3 j))) i)
      = (Matrix.gram ℝ (fun i : Fin 5 => toE (b i))).submatrix finSumFinEquiv finSumFinEquiv := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.submatrix_apply, Matrix.gram_apply, Matrix.gram_apply]
  cases i <;> cases j <;>
    simp [pair, idx3, inner_toE, finSumFinEquiv_inl, finSumFinEquiv_inr]

/-- `det (gram)` of the projected three vectors `π (b 2), π (b 3), π (b 4)`. -/
lemma det_gram_proj_eq (hb : Λ = Submodule.span ℤ (Set.range (pair b)))
    (hli : LinearIndependent ℝ (fun i : Fin 5 => toE (b i)))
    (h5 : (Matrix.gram ℝ (fun i : Fin 5 => toE (b i))).det = 1) :
    (Matrix.gram ℝ (fun j : Fin 3 => proj Λ (toE (b (idx3 j))))).det = 1 / detL Λ ^ 2 := by
  have hg := gram_proj_det' (E := E5) (fun i : Fin 2 => toE (pair b i))
    (fun j : Fin 3 => toE (b (idx3 j))) (pair_linIndep hli)
  have hW : (Submodule.span ℝ (Set.range fun i : Fin 2 => toE (pair b i)))ᗮ = W Λ := by
    rw [W, ← Lℝ_eq_of_basis hb]
  have hproj : (fun j : Fin 3 =>
        (Submodule.span ℝ (Set.range fun i : Fin 2 => toE (pair b i)))ᗮ.starProjection
          (toE (b (idx3 j)))) = fun j : Fin 3 => proj Λ (toE (b (idx3 j))) := by
    funext j
    refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
    · rw [hW, proj]
      exact Submodule.starProjection_apply_mem (W Λ) _
    · rw [hW, proj]
      exact Submodule.sub_starProjection_mem_orthogonal _
  rw [hproj] at hg
  rw [gram_sumElim_eq b, Matrix.det_submatrix_equiv_self, h5,
    det_gram_pair_eq hb hli] at hg
  have hpos : detL Λ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (detL_pos hb hli))
  rw [mul_comm] at hg
  rw [eq_div_iff hpos]
  exact hg.symm

/-- The `Ggen` span `W Λ` over `ℝ`. -/
lemma span_Ggen_top (hb : Λ = Submodule.span ℤ (Set.range (pair b)))
    (hli : LinearIndependent ℝ (fun i : Fin 5 => toE (b i))) :
    ⊤ ≤ Submodule.span ℝ (Set.range (Ggen b Λ)) := by
  rw [← span_ℝ_ΓW_eq_top, (Gamma_span_indep b Λ hb hli).1, Submodule.span_span_of_tower ℤ]

/-- The `ℝ`-basis of `W Λ` given by `π (b 2), π (b 3), π (b 4)`. -/
noncomputable def Wbasis (b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ))
    (Λ : Submodule ℤ (Fin 5 → ℤ)) (hb : Λ = Submodule.span ℤ (Set.range (pair b)))
    (hli : LinearIndependent ℝ (fun i : Fin 5 => toE (b i))) : Module.Basis (Fin 3) ℝ (W Λ) :=
  basisOfTopLeSpanOfCardEqFinrank (Ggen b Λ) (span_Ggen_top hb hli) (by
    rw [finrank_W hb hli]
    simp)

@[simp] lemma Wbasis_apply (hb : Λ = Submodule.span ℤ (Set.range (pair b)))
    (hli : LinearIndependent ℝ (fun i : Fin 5 => toE (b i))) (j : Fin 3) :
    Wbasis b Λ hb hli j = Ggen b Λ j :=
  congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) j

/-- `ΓW Λ` is the `ℤ`-span of the `ℝ`-basis `Wbasis`. -/
lemma ΓW_eq_span_Wbasis (hb : Λ = Submodule.span ℤ (Set.range (pair b)))
    (hli : LinearIndependent ℝ (fun i : Fin 5 => toE (b i))) :
    ΓW Λ = Submodule.span ℤ (Set.range (Wbasis b Λ hb hli)) := by
  rw [(Gamma_span_indep b Λ hb hli).1]
  congr 1
  rw [show ⇑(Wbasis b Λ hb hli) = (fun j => Ggen b Λ j) from funext (Wbasis_apply hb hli)]

/-- The covolume of `ΓW Λ` in `W Λ` is `1 / detL Λ`. -/
lemma covolume_ΓW (hb : Λ = Submodule.span ℤ (Set.range (pair b)))
    (hli : LinearIndependent ℝ (fun i : Fin 5 => toE (b i)))
    (h5 : (Matrix.gram ℝ (fun i : Fin 5 => toE (b i))).det = 1) :
    ZLattice.covolume (ΓW Λ) = 1 / detL Λ := by
  let g := Wbasis b Λ hb hli
  have hg_apply : ∀ j, g j = Ggen b Λ j := fun j => Wbasis_apply hb hli j
  have hΓg : ΓW Λ = Submodule.span ℤ (Set.range g) := ΓW_eq_span_Wbasis hb hli
  haveI hdisc : DiscreteTopology ↥(Submodule.span ℤ (Set.range g)) := inferInstance
  haveI hzl : IsZLattice ℝ (Submodule.span ℤ (Set.range g)) := inferInstance
  have hcast_inj : Function.Injective fun r : ℤ => r • (1 : ℝ) := by
    intro a c hac
    exact Int.cast_injective (α := ℝ) (by simpa using hac)
  let gZ : Module.Basis (Fin 3) ℤ ↥(Submodule.span ℤ (Set.range g)) :=
    Module.Basis.mk (v := fun j => (⟨g j, Submodule.subset_span ⟨j, rfl⟩⟩ :
        ↥(Submodule.span ℤ (Set.range g))))
      (by
        refine LinearIndependent.of_comp (Submodule.subtype (Submodule.span ℤ (Set.range g))) ?_
        simpa only [Function.comp_def, Submodule.coe_subtype, Subtype.coe_mk] using
          (LinearIndependent.restrict_scalars (R := ℤ) hcast_inj g.linearIndependent))
      (by
        intro x _
        have hx : (x : (W Λ)) ∈ Submodule.span ℤ (Set.range g) := x.2
        refine Submodule.span_induction (p := fun y hy => (⟨y, hy⟩ :
            ↥(Submodule.span ℤ (Set.range g))) ∈ Submodule.span ℤ (Set.range fun j =>
              (⟨g j, Submodule.subset_span ⟨j, rfl⟩⟩ : ↥(Submodule.span ℤ (Set.range g)))))
          ?_ ?_ ?_ ?_ hx
        · rintro y ⟨j, rfl⟩
          exact Submodule.subset_span ⟨j, rfl⟩
        · exact Submodule.zero_mem (Submodule.span ℤ (Set.range fun j =>
              (⟨g j, Submodule.subset_span ⟨j, rfl⟩⟩ : ↥(Submodule.span ℤ (Set.range g)))))
        · intro y z hy hz hhy hhz
          exact Submodule.add_mem _ hhy hhz
        · intro c y hy hhy
          exact Submodule.smul_mem _ c hhy)
  have gZ_apply : ∀ j, ((gZ j : ↥(Submodule.span ℤ (Set.range g))) : (W Λ)) = g j := by
    intro j
    exact congrArg Subtype.val (Module.Basis.mk_apply _ _ j)
  have e3 : Fin (Module.finrank ℝ (W Λ)) ≃ Fin 3 := finCongr (finrank_W hb hli)
  have hgrameq : (Matrix.gram ℝ (fun i : Fin (Module.finrank ℝ (W Λ)) =>
        (((gZ.reindex e3.symm i : ↥(Submodule.span ℤ (Set.range g)))) : (W Λ))))
      = (Matrix.gram ℝ (fun j : Fin 3 => proj Λ (toE (b (idx3 j))))).submatrix e3 e3 := by
    ext i k
    rw [Matrix.submatrix_apply, Matrix.gram_apply, Matrix.gram_apply, Submodule.coe_inner]
    simp only [Module.Basis.reindex_apply, gZ_apply, hg_apply, Ggen, Equiv.symm_symm]
  have hcov := covolume_eq_gram_det (E := (W Λ)) (L := Submodule.span ℤ (Set.range g))
    (gZ.reindex e3.symm)
  rw [hgrameq, Matrix.det_submatrix_equiv_self, det_gram_proj_eq hb hli h5] at hcov
  rw [← hΓg] at hcov
  rw [hcov, show (1 : ℝ) / detL Λ ^ 2 = (1 / detL Λ) ^ 2 by rw [div_pow, one_pow],
    Real.sqrt_sq (le_of_lt (one_div_pos.mpr (detL_pos hb hli)))]


end Covolume

end

end Work.HP.Q44Child
