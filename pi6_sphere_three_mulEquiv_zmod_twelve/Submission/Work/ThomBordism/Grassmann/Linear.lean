import Submission.Work.ThomBordism.Grassmann.Frame

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The linear algebra behind the charts of the oriented Grassmannian

For a frame `f : Fin k → ℝ^{k+m}` and a `k`-element set `S` of coordinates, the chart condition
"the coordinate projection `p_S` is an isomorphism onto the plane spanned by `f`" is
`(frameMatrix S f).det ≠ 0`.  This module proves the two facts about it that the construction of
the oriented Grassmannian needs:

* **Coverage** (`Work.ThomBordism.Grassmann.exists_chartIdx_det_ne_zero`): every linearly
  independent frame has a nonvanishing `S`-minor.  The proof takes the quotient of `ℝ^{k+m}` by the
  plane `P` spanned by the frame (dimension `m`), extracts a basis `g` of that quotient from the
  spanning family of the images of the coordinate vectors
  (`Submodule.exists_fun_fin_finrank_span_eq`), pulls the basis back to `m` coordinates `T`, and
  takes `S` to be the complementary `k` coordinates: the coordinates in `T` are "independent
  modulo `P`", so they give a complement of `P`.
* The **identification** (`toLin'_frameMatrix`) of the linear map of the matrix `frameMatrix S f`
  with the composite of the coordinate projection `coordProj S` with the coordinate map
  `coeffMap f`.  This turns `det (frameMatrix S f) ≠ 0` into the kernel condition
  `ker (coordProj S ∘ coeffMap f) = ⊥`.
-/

namespace Work.ThomBordism.Grassmann

open scoped Topology

noncomputable section

variable {k m : ℕ}

/-- The **coordinate map** of a frame: `v ↦ ∑ j, v j • f j`, expressed in the coordinates of
`ℝ^{k+m}` (so that its values are `Fin (k+m) → ℝ`, not `Amb (k+m)`). -/
def coeffMap (f : Fin k → Amb (k+m)) : (Fin k → ℝ) →ₗ[ℝ] (Fin (k+m) → ℝ) :=
  LinearMap.pi fun x => ∑ j, EuclideanSpace.proj (𝕜 := ℝ) x (f j) • LinearMap.proj j

theorem coeffMap_apply (f : Fin k → Amb (k+m)) (v : Fin k → ℝ) (x : Fin (k+m)) :
    coeffMap f v x = ∑ j, v j * EuclideanSpace.proj (𝕜 := ℝ) x (f j) := by
  simp only [coeffMap, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The **coordinate projection** onto the coordinates in `S`, in the order induced by
`Finset.equivFinOfCardEq`. -/
def coordProj (S : ChartIdx k m) : (Fin (k+m) → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
  LinearMap.pi fun i =>
    LinearMap.proj (((S.1.equivFinOfCardEq S.2).symm i : ↥S.1) : Fin (k+m))

theorem coordProj_apply (S : ChartIdx k m) (w : Fin (k+m) → ℝ) (i : Fin k) :
    coordProj S w i = w (((S.1.equivFinOfCardEq S.2).symm i : ↥S.1) : Fin (k+m)) := by
  simp only [coordProj, LinearMap.pi_apply, LinearMap.proj_apply]

/-- `coordProj S` is the projection onto the coordinates in `S`. -/
theorem coordProj_eq_zero_iff (S : ChartIdx k m) (w : Fin (k+m) → ℝ) :
    coordProj S w = 0 ↔ ∀ y : Fin (k+m), y ∈ S.1 → w y = 0 := by
  constructor
  · intro h y hy
    have h' := congrFun h ((S.1.equivFinOfCardEq S.2) ⟨y, hy⟩)
    simpa [coordProj_apply] using h'
  · intro h
    funext i
    rw [coordProj_apply]
    exact h _ ((S.1.equivFinOfCardEq S.2).symm i).2

/-- The entries of the matrix `frameMatrix S f` are the values of the coordinate map on the
standard basis vectors. -/
theorem frameMatrix_eq_coeffMap (S : ChartIdx k m) (f : Fin k → Amb (k+m)) (i j : Fin k) :
    frameMatrix S f i j =
      coeffMap f (Pi.single j 1) (((S.1.equivFinOfCardEq S.2).symm i : ↥S.1) : Fin (k+m)) := by
  rw [coeffMap_apply]
  simp only [frameMatrix]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **The matrix `frameMatrix S f` is the matrix of `coordProj S ∘ coeffMap f`**: going from a
coefficient vector to the `S`-coordinates of the corresponding linear combination is exactly
multiplying by `frameMatrix S f`. -/
theorem toLin'_frameMatrix (S : ChartIdx k m) (f : Fin k → Amb (k+m)) :
    Matrix.toLin' (frameMatrix S f) = (coordProj S).comp (coeffMap f) := by
  apply LinearMap.ext
  intro v
  funext i
  simp only [Matrix.toLin'_apply, Matrix.mulVec_apply, LinearMap.comp_apply, coordProj_apply,
    coeffMap_apply, dotProduct, Matrix.row, Matrix.row_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [frameMatrix]; ring


/-- `c • e_y = ` the vector with `c` in coordinate `y`. -/
theorem smul_single_one {n : ℕ} (c : ℝ) (y : Fin n) :
    (c • (Pi.single y (1 : ℝ) : Fin n → ℝ)) = Pi.single y c := by
  funext z
  by_cases h : z = y
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

/-- **The coordinate map of a linearly independent frame is injective.** -/
theorem coeffMap_injective (f : Fin k → Amb (k+m)) (hf : LinearIndependent ℝ f) :
    Function.Injective (coeffMap f) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  have hv0 : coeffMap f v = 0 := LinearMap.mem_ker.mp hv
  have hzero : (∑ j, v j • f j : Amb (k+m)) = 0 := by
    apply WithLp.ofLp_injective
    funext x
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_zero, Finset.sum_apply,
      Pi.smul_apply, Pi.zero_apply]
    have h := congrFun hv0 x
    rw [coeffMap_apply] at h
    simpa [mul_comm] using h
  have h2 := (Fintype.linearIndependent_iff.mp hf) v hzero
  funext j
  simpa using h2 j

/-- The standard basis vectors span `ℝⁿ`. -/
theorem span_range_single_one {n : ℕ} :
    Submodule.span ℝ (Set.range fun x : Fin n => (Pi.single x (1 : ℝ) : Fin n → ℝ)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro w
  rw [← Finset.univ_sum_single w]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [← smul_single_one (w x) x]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)

/-- **The key linear-algebra input of the chart cover.**  For a linearly independent frame `f` there
are `k` coordinates `S` whose coordinate projection is injective on the plane spanned by `f`, i.e.
`range (coeffMap f) ⊓ ker (coordProj S) = ⊥`.

The proof passes to the quotient `Q = ℝ^{k+m} / P` of dimension `m`; the images of the standard
basis vectors span `Q`, and `Submodule.exists_fun_fin_finrank_span_eq` extracts from them an
independent family of size `finrank Q = m`; pulling the chosen basis vectors back to coordinates
gives the `m`-element set `T`, and `S` is its complement. -/
theorem exists_chartIdx_range_inf_ker_eq_bot (f : Fin k → Amb (k+m))
    (hf : LinearIndependent ℝ f) :
    ∃ S : ChartIdx k m,
      LinearMap.range (coeffMap f) ⊓ LinearMap.ker (coordProj S) = ⊥ := by
  classical
  have hΦker : (coeffMap f).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (coeffMap_injective f hf)
  have hPfin : Module.finrank ℝ (LinearMap.range (coeffMap f)) = k := by
    have h := LinearMap.finrank_range_add_finrank_ker (coeffMap f)
    rw [hΦker, finrank_bot, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  have hQfin : Module.finrank ℝ ((Fin (k+m) → ℝ) ⧸ LinearMap.range (coeffMap f)) = m := by
    have h := Submodule.finrank_quotient_add_finrank (LinearMap.range (coeffMap f))
    rw [hPfin, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  have hspan : Submodule.span ℝ (Set.range fun x : Fin (k+m) =>
      (LinearMap.range (coeffMap f)).mkQ (Pi.single x (1 : ℝ))) = ⊤ := by
    calc Submodule.span ℝ (Set.range fun x : Fin (k+m) =>
            (LinearMap.range (coeffMap f)).mkQ (Pi.single x (1 : ℝ)))
        = Submodule.map ((LinearMap.range (coeffMap f)).mkQ) (Submodule.span ℝ
            (Set.range fun x : Fin (k+m) => (Pi.single x (1 : ℝ) : Fin (k+m) → ℝ))) := by
          rw [Submodule.map_span]
          congr 1
          exact Set.range_comp _ _
      _ = Submodule.map ((LinearMap.range (coeffMap f)).mkQ) ⊤ := by rw [span_range_single_one]
      _ = LinearMap.range ((LinearMap.range (coeffMap f)).mkQ) :=
          (LinearMap.range_eq_map _).symm
      _ = ⊤ := LinearMap.range_eq_top.mpr
          (Submodule.Quotient.mk_surjective (LinearMap.range (coeffMap f)))
  have hfins : Module.finrank ℝ (Submodule.span ℝ (Set.range fun x : Fin (k+m) =>
      (LinearMap.range (coeffMap f)).mkQ (Pi.single x (1 : ℝ)))) = m := by
    rw [hspan, finrank_top]
    exact hQfin
  obtain ⟨g, hg_mem, -, hg_li⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ
      (Set.range fun x : Fin (k+m) => (LinearMap.range (coeffMap f)).mkQ (Pi.single x (1 : ℝ)))
  let e : Fin (Module.finrank ℝ (Submodule.span ℝ (Set.range fun x : Fin (k+m) =>
      (LinearMap.range (coeffMap f)).mkQ (Pi.single x (1 : ℝ))))) ≃ Fin m := finCongr hfins
  let g' : Fin m → ((Fin (k+m) → ℝ) ⧸ LinearMap.range (coeffMap f)) := fun i => g (e.symm i)
  have hg'_li : LinearIndependent ℝ g' := hg_li.comp e.symm e.symm.injective
  have hg'_mem : ∀ i : Fin m, g' i ∈ Set.range fun x : Fin (k+m) =>
      (LinearMap.range (coeffMap f)).mkQ (Pi.single x (1 : ℝ)) := fun i => hg_mem _
  choose xx hxx using hg'_mem
  have hxx_inj : Function.Injective xx := by
    intro i j hij
    refine hg'_li.injective ?_
    rw [← hxx i, ← hxx j, hij]
  refine ⟨⟨Finset.univ \ Finset.univ.image xx, ?_⟩, ?_⟩
  · rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
      Finset.card_image_of_injective _ hxx_inj, Finset.card_univ, Fintype.card_fin]
    omega
  · rw [Submodule.eq_bot_iff]
    intro w hw
    obtain ⟨hwP, hwker⟩ := Submodule.mem_inf.mp hw
    have hwvanish : ∀ y ∈ (Finset.univ \ Finset.univ.image xx : Finset (Fin (k+m))), w y = 0 :=
      (coordProj_eq_zero_iff _ w).mp (LinearMap.mem_ker.mp hwker)
    have hqw : (LinearMap.range (coeffMap f)).mkQ w = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hwP
    have hsingle : (∑ i : Fin m, w (xx i) • (Pi.single (xx i) (1 : ℝ) : Fin (k+m) → ℝ)) = w := by
      rw [← Finset.sum_image (s := Finset.univ) (g := xx)
        (f := fun y => w y • (Pi.single y (1 : ℝ) : Fin (k+m) → ℝ)) hxx_inj.injOn]
      rw [Finset.sum_subset (Finset.subset_univ _) (fun y _ hy => by
        rw [show w y = 0 from hwvanish y (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩),
          zero_smul])]
      rw [Finset.sum_congr rfl fun y _ => smul_single_one (w y) y]
      exact Finset.univ_sum_single w
    have hcomb : ∑ i : Fin m, w (xx i) • g' i = 0 := by
      have h1 : ∑ i : Fin m, w (xx i) • g' i
          = ∑ i : Fin m, (LinearMap.range (coeffMap f)).mkQ
              (w (xx i) • (Pi.single (xx i) (1 : ℝ) : Fin (k+m) → ℝ)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, ← hxx i]
      rw [h1, ← map_sum, hsingle]
      exact hqw
    have hwxx : ∀ i : Fin m, w (xx i) = 0 :=
      (Fintype.linearIndependent_iff.mp hg'_li) (fun i => w (xx i)) hcomb
    rw [← Finset.univ_sum_single w]
    refine Finset.sum_eq_zero fun y _ => ?_
    have hy0 : w y = 0 := by
      by_cases hy : y ∈ Finset.univ.image xx
      · obtain ⟨i, -, hiy⟩ := Finset.mem_image.mp hy
        rw [← hiy]; exact hwxx i
      · exact hwvanish y (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩)
    rw [hy0]
    simp

/-- From the separation condition `range Φ ⊓ ker g = ⊥` (with `Φ` injective) one gets
`ker (g ∘ Φ) = ⊥`. -/
theorem ker_comp_eq_bot_of_inf_eq_bot {Φ : (Fin k → ℝ) →ₗ[ℝ] (Fin (k+m) → ℝ)}
    (hΦ : Function.Injective Φ) {g : (Fin (k+m) → ℝ) →ₗ[ℝ] (Fin k → ℝ)}
    (h : LinearMap.range Φ ⊓ LinearMap.ker g = ⊥) : LinearMap.ker (g.comp Φ) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hv' : (g.comp Φ) v = 0 := LinearMap.mem_ker.mp hv
  have hmem : Φ v ∈ LinearMap.range Φ ⊓ LinearMap.ker g :=
    ⟨⟨v, rfl⟩, by
      show g (Φ v) = 0
      exact hv'⟩
  rw [h] at hmem
  have h0 : Φ v = 0 := by simpa using hmem
  exact hΦ (by simpa using h0 : Φ v = Φ 0)

/-- **Coverage of the charts, in kernel form.** -/
theorem exists_chartIdx_ker_eq_bot (f : Fin k → Amb (k+m)) (hf : LinearIndependent ℝ f) :
    ∃ S : ChartIdx k m, LinearMap.ker ((coordProj S).comp (coeffMap f)) = ⊥ := by
  obtain ⟨S, hS⟩ := exists_chartIdx_range_inf_ker_eq_bot f hf
  exact ⟨S, ker_comp_eq_bot_of_inf_eq_bot (coeffMap_injective f hf) hS⟩

/-- The chart condition `det ≠ 0` is exactly the kernel condition on the coordinate map. -/
theorem det_ne_zero_iff_ker (S : ChartIdx k m) (f : Fin k → Amb (k+m)) :
    (frameMatrix S f).det ≠ 0 ↔ LinearMap.ker ((coordProj S).comp (coeffMap f)) = ⊥ := by
  rw [← LinearMap.det_toLin' (frameMatrix S f), toLin'_frameMatrix]
  rw [ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot (f := (coordProj S).comp (coeffMap f))]
  simp only [ne_eq, not_not]

/-- **Coverage of the charts**: every linearly independent frame has a nonvanishing `S`-minor. -/
theorem exists_chartIdx_det_ne_zero (f : Fin k → Amb (k+m)) (hf : LinearIndependent ℝ f) :
    ∃ S : ChartIdx k m, (frameMatrix S f).det ≠ 0 := by
  obtain ⟨S, hS⟩ := exists_chartIdx_ker_eq_bot f hf
  exact ⟨S, (det_ne_zero_iff_ker S f).mpr hS⟩

end

end Work.ThomBordism.Grassmann
