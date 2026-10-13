/-
  Area E7, `Π_{K+1}` case of `CoreLT_succ`: the algebra of the fibre-critical set.

  `Work.WilE7.CoreStep.finrank_projTop_of_not_critSet`: on a fibrewise stratum `S` of fibre
  codimension `S.j = m` inside `ℝ^{n+(m+1)}`, at a point `z` of `S` which is **not** a
  fibre-critical point of the *last* fibre coordinate (`z ∉ critSet S (Fin.last m)`), the
  `(n+1)`-projection `projTopLin n m` (the first `n` coordinates together with the last fibre
  coordinate) is surjective on the tangent space `ker (jac S z)`, so its image has the full
  dimension `n + 1`.

  The mathematics.  Write `A = (∂_{y_{l'}} f_a(z))` for the `m × (m+1)` matrix of fibre
  derivatives of the defining equations `f_a = S.h a` and `e = e_last` for the coordinate
  functional of the last fibre coordinate.  `critSet S (Fin.last m)` is by definition the locus
  where *all* maximal `(m+1) × (m+1)` minors of the augmented matrix `[∂_y f ; e]` vanish, so
  `z ∉ critSet S (Fin.last m)` gives a non-vanishing maximal minor.  The augmented matrix has
  block form `[[A, c], [0, 1]]` with the last row equal to `e`, hence a non-vanishing maximal
  minor forces its rank to be `m+1` (a non-vanishing maximal minor bounds the rank from below
  by `Matrix.rank_submatrix_le`, and `Matrix.rank_le_card_height` bounds it from above); as it
  is a square matrix, `[∂_y f ; e]` is injective, and then the *middle* block `A'` (the fibre
  coordinates other than the last one) is injective as well: a vector `u` in the kernel of `A'`,
  extended by `0` in the last coordinate, is killed by `[∂_y f ; e]`.

  Injectivity of the middle block is what the projection needs.  Let `w ∈ ker (jac S z)` with
  `projTopLin n m w = 0`.  The vanishing of the first `n` coordinates and of the last fibre
  coordinate, substituted into the `S.j` equations `jac S z · w = 0`, leaves exactly the system
  `A' · (w ∘ y) = 0` for the middle fibre coordinates; injectivity of `A'` gives `w = 0`.  So
  `projTopLin n m` is injective on `ker (jac S z)`, and a rank–nullity count
  (`finrank (ker (jac S z)) ≥ n + 1`, as `jac S z` maps into `ℝ^{S.j}` with `S.j = m`, against
  `finrank ((ker (jac S z)).map (projTopLin n m)) ≤ n + 1` inside `ℝ^{n+1}`) gives the claim.

  The two ingredients are `middle_ker_bot_of_nonzero_minor` (pure linear algebra of the block
  matrix) and `ker_proj_bot_of_middle_ker_bot` (the index bookkeeping splitting
  `ℝ^{n+(m+1)} = ℝ^n × ℝ^m × ℝ`), with `det_submatrix_aug` identifying the critical minors of
  `FiberCutDefs` with the minors of the evaluated derivative matrix.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.FibreEndDefs
import Submission.Work.WilE7.FiberCutDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.CoreStep

open WilkiesDesign WilkiesDesign.E

/-! ## 1. Linear algebra of the augmented matrix `[∂_y f ; e_last]` -/

/-- A non-vanishing maximal minor of `Aug` forces `Aug` to have full row rank. -/
theorem rank_eq_height_of_nonzero_minor {j m : ℕ} (Aug : Matrix (Fin (j + 1)) (Fin (m + 1)) ℝ)
    (hmin : ∃ σ : Fin (j + 1) → Fin (m + 1), (Aug.submatrix id σ).det ≠ 0) :
    Aug.rank = j + 1 := by
  obtain ⟨σ, hσ⟩ := hmin
  have h1 : (Aug.submatrix id σ).rank = j + 1 := by
    rw [Matrix.rank_of_det_ne_zero hσ, Fintype.card_fin]
  have h2 : (Aug.submatrix id σ).rank ≤ Aug.rank := Matrix.rank_submatrix_le Aug id σ
  have h3 : Aug.rank ≤ j + 1 := by simpa using Matrix.rank_le_card_height Aug
  omega

/-- **The algebra of the fibre-critical set.**

Let `Aug : Matrix (Fin (j+1)) (Fin (m+1)) ℝ` be the evaluated matrix `[∂_y f ; e]` of fibre
derivatives of the defining equations `f = h` augmented by the coordinate functional `e` of the
last fibre coordinate: its `a`-th row for `a : Fin j` is `a ↦ ∂_{y_{l'}} h_a(z)` and its last row
is `e`.  If some maximal minor of `Aug` does not vanish, then the *middle block* — the rows
`Fin j` against the fibre coordinates other than the last one — has trivial kernel (it is
invertible, as `j = m`).

Indeed `Aug` has full row rank `j + 1` (`rank_eq_height_of_nonzero_minor`), and `j + 1 = m + 1`
is also the number of columns, so `Aug` is injective; a vector `u` in the kernel of the middle
block, padded by `0` in the last coordinate, is in the kernel of `Aug`, hence is `0`. -/
theorem middle_ker_bot_of_nonzero_minor {j m : ℕ} (Aug : Matrix (Fin (j+1)) (Fin (m+1)) ℝ)
    (hlast : ∀ l' : Fin (m+1), Aug (Fin.last j) l' = if l' = Fin.last m then 1 else 0)
    (hj : j = m)
    (hmin : ∃ σ : Fin (j+1) → Fin (m+1), (Aug.submatrix id σ).det ≠ 0) :
    LinearMap.ker (Matrix.of (fun (a : Fin j) (c : Fin m) =>
      Aug (Fin.castSucc a) (Fin.castSucc c))).mulVecLin = ⊥ := by
  classical
  have hrank : Aug.rank = j + 1 := rank_eq_height_of_nonzero_minor Aug hmin
  -- `Aug` is injective: full row rank and as many columns as rows.
  have hkerAug : LinearMap.ker Aug.mulVecLin = ⊥ := by
    rw [← Submodule.finrank_eq_zero]
    have h := LinearMap.finrank_range_add_finrank_ker Aug.mulVecLin
    have hrange : Module.finrank ℝ (LinearMap.range Aug.mulVecLin) = j + 1 := by
      rw [← Matrix.rank, hrank]
    have hdom : Module.finrank ℝ (Fin (m+1) → ℝ) = m + 1 := by simp
    omega
  rw [Matrix.ker_mulVecLin_eq_bot_iff]
  intro u hu
  let u' : Fin (m+1) → ℝ := Fin.lastCases (0:ℝ) u
  have hz : Aug.mulVec u' = 0 := by
    funext a
    rcases Fin.eq_castSucc_or_eq_last a with ⟨a₀, rfl⟩ | rfl
    · show Aug.mulVec u' a₀.castSucc = 0
      rw [Matrix.mulVec_apply, dotProduct, Fin.sum_univ_castSucc]
      simp only [Matrix.row, u', Fin.lastCases_castSucc, Fin.lastCases_last, mul_zero, add_zero]
      have h := congrFun hu a₀
      rw [Matrix.mulVec_apply, dotProduct] at h
      simpa [Matrix.of_apply] using h
    · show Aug.mulVec u' (Fin.last j) = 0
      rw [Matrix.mulVec_apply, dotProduct, Fin.sum_univ_castSucc]
      simp [hlast, u', Fin.lastCases_last, Fin.lastCases_castSucc]
  have hzero : u' = 0 :=
    (LinearMap.ker_eq_bot'.mp hkerAug) u' (by rw [Matrix.mulVecLin_apply]; exact hz)
  funext c
  have h := congrFun hzero c.castSucc
  simpa [u'] using h

/-! ## 2. Splitting `ℝ^{n+(m+1)} = ℝ^n × ℝ^m × ℝ` -/

/-- **The projection `projTopLin` is injective on the tangent space.**  If the middle block `A`
of the Jacobian `Jac` (the fibre coordinates other than the last one) is invertible, then
`projTopLin n m` — the first `n` coordinates together with the last one — has trivial kernel on
`ker Jac.mulVecLin`.

Indeed, if `w ∈ ker Jac` has `projTopLin n m w = 0`, then the first `n` and the last coordinates
of `w` vanish, so the equations `Jac · w = 0` reduce (after splitting the sums along
`Fin (n + (m+1)) = Fin n ⊕ Fin (m+1)` and `Fin (m+1) = Fin m ⊕ Fin 1`) to
`A · (w ∘ natAdd n ∘ castSucc) = 0`, whence the middle fibre coordinates of `w` vanish too, and
`w = 0`. -/
theorem ker_proj_bot_of_middle_ker_bot {n m j : ℕ} (Jac : Matrix (Fin j) (Fin (n + (m+1))) ℝ)
    (A : Matrix (Fin j) (Fin m) ℝ)
    (hcol : ∀ (a : Fin j) (c : Fin m), A a c = Jac a (Fin.natAdd n (Fin.castSucc c)))
    (hker : LinearMap.ker A.mulVecLin = ⊥) :
    LinearMap.ker ((projTopLin n m).comp (LinearMap.ker Jac.mulVecLin).subtype) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro ⟨w, hw⟩ hmem
  have hproj : projTopLin n m w = 0 := hmem
  have hJac : Jac.mulVec w = 0 := by
    rw [← Matrix.mulVecLin_apply]
    simpa only [LinearMap.mem_ker] using hw
  -- the first `n` coordinates of `w` vanish
  have hbase : ∀ i : Fin n, w (Fin.castAdd (m+1) i) = 0 := by
    intro i
    have hh := congrFun hproj i.castSucc
    rw [projTopLin_apply, projTop_castSucc] at hh
    simpa [WilkiesDesign.E.projFirst] using hh
  -- the last fibre coordinate of `w` vanishes
  have htop : w (Fin.natAdd n (Fin.last m)) = 0 := by
    have hh := congrFun hproj (Fin.last n)
    rw [projTopLin_apply, projTop_last] at hh
    simpa [WilkiesDesign.E.projSnd] using hh
  -- the equations reduce to `A · (middle part of w) = 0`
  have hu : A.mulVec (fun c : Fin m => w (Fin.natAdd n (Fin.castSucc c))) = 0 := by
    funext a
    rw [Matrix.mulVec_apply, dotProduct]
    have h0 : ∑ l : Fin (n + (m+1)), Jac a l * w l = 0 := by
      have hh := congrFun hJac a
      rw [Matrix.mulVec_apply, dotProduct] at hh
      simpa [Matrix.row] using hh
    rw [Fin.sum_univ_add] at h0
    have h1 : (∑ i : Fin n, Jac a (Fin.castAdd (m+1) i) * w (Fin.castAdd (m+1) i)) = 0 :=
      Finset.sum_eq_zero (fun i _ => by rw [hbase i, mul_zero])
    rw [h1, zero_add] at h0
    rw [Fin.sum_univ_castSucc] at h0
    have h2 : Jac a (Fin.natAdd n (Fin.last m)) * w (Fin.natAdd n (Fin.last m)) = 0 := by
      rw [htop, mul_zero]
    rw [h2, add_zero] at h0
    calc A.mulVec (fun c : Fin m => w (Fin.natAdd n (Fin.castSucc c))) a
        = A.row a ⬝ᵥ (fun c : Fin m => w (Fin.natAdd n (Fin.castSucc c))) := rfl
      _ = ∑ c : Fin m, A a c * w (Fin.natAdd n (Fin.castSucc c)) := by
          simp [dotProduct, Matrix.row]
      _ = ∑ c : Fin m, Jac a (Fin.natAdd n (Fin.castSucc c)) * w (Fin.natAdd n (Fin.castSucc c)) := by
          exact Finset.sum_congr rfl (fun c _ => by rw [hcol a c])
      _ = 0 := h0
  have hmid : ∀ c : Fin m, w (Fin.natAdd n (Fin.castSucc c)) = 0 := by
    have h0 : (fun c : Fin m => w (Fin.natAdd n (Fin.castSucc c))) = 0 :=
      (LinearMap.ker_eq_bot'.mp hker) _ hu
    intro c
    have h := congrFun h0 c
    simpa using h
  refine Subtype.ext ?_
  funext l
  refine Fin.addCases (motive := fun l => w l = 0) (fun i => hbase i) (fun c => ?_) l
  rcases Fin.eq_castSucc_or_eq_last c with ⟨c', rfl⟩ | rfl
  · exact hmid c'
  · exact htop

/-! ## 3. The critical minors are the minors of the evaluated derivative matrix -/

/-- The derivative of a coordinate function at a coordinate direction is the Kronecker delta:
`∂_{x_i} x_m = δ_{i m}`. -/
private theorem eaEval_eaD_X_inl {k r : ℕ} (c : EAChain k r) (i m : Fin k) (z : Fin k → ℝ) :
    eaEval c (eaD c i (MvPolynomial.X (Sum.inl m))) z = if i = m then 1 else 0 := by
  rw [eaD]
  have hsum : (∑ k' : Fin r, MvPolynomial.C (c.a k' i) * MvPolynomial.X (Sum.inr k') *
      MvPolynomial.pderiv (Sum.inr k') (MvPolynomial.X (Sum.inl m))) = 0 := by
    refine Finset.sum_eq_zero (fun k' _ => ?_)
    rw [MvPolynomial.pderiv_X_of_ne (i := Sum.inr k') (j := Sum.inl m) (by simp)]
    simp
  rw [hsum, add_zero, MvPolynomial.pderiv_X]
  simp [eaEval, Pi.single_apply, Sum.inl.injEq, eq_comm]

/-- `Fin.lastCases` read off a function at the last argument and at the `castSucc` arguments. -/
private theorem lastCases_apply_comp {α : Sort*} {n : ℕ} (d : Fin (n+1) → α) (i : Fin (n+1)) :
    Fin.lastCases (d (Fin.last n)) (fun i : Fin n => d i.castSucc) i = d i := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Fin.lastCases_castSucc]
  · rw [Fin.lastCases_last]

/-- The evaluated critical minor `critMinor c h (Fin.last m) σ` is the `σ`-minor of the evaluated
matrix `[∂_y h ; e_last]` of fibre derivatives. -/
private theorem eaEval_critMinor_eq_det {n m r j : ℕ} (c : EAChain (n + (m+1)) r)
    (h : Fin j → EAPoly (n + (m+1)) r) (z : Fin (n + (m+1)) → ℝ)
    (σ : Fin (j+1) → Fin (m+1)) :
    ((Matrix.of (fun (a : Fin (j+1)) (l' : Fin (m+1)) =>
        eaEval c (eaD c (Fin.natAdd n l')
          (Fin.lastCases (MvPolynomial.X (Sum.inl (Fin.natAdd n (Fin.last m)))) h a)) z)).submatrix
        id σ).det
      = eaEval c (Work.WilE7.critMinor c h (Fin.last m) σ) z := by
  rw [Work.WilE7.critMinor]
  rw [Work.WilE5.eaEval_detOp]
  simp only [Work.WilE7.fibDir]
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.of_apply, id_eq]
  rw [lastCases_apply_comp (fun b : Fin (j+1) => Fin.natAdd n (σ b)) b]

/-! ## 4. The main theorem -/

/-- **The algebra of the fibre-critical set, for `FiberCutDefs`.**

This is `Work.WilE7.CoreStep.finrank_projTop_of_not_critSet` as requested by the `Π_{K+1}` case
of `CoreLT_succ`.  Only the hypotheses `hj : S.j = m` and `hzc : z ∉ critSet S (Fin.last m)` are
used: the non-vanishing critical minor alone forces the fibre Jacobian to be "unimodular in the
last coordinate", and the two assertions `S.Good` and `z ∈ S.X.set` are not needed for this
purely algebraic step (the rank of `jac S z` is bounded from above by its codimension `S.j`, which
is all the dimension count uses).  They are kept in the statement for the caller. -/
theorem finrank_projTop_of_not_critSet {n m : ℕ} (S : WilkiesDesign.E.Stratum n (m + 1))
    (hS : S.Good) (hj : S.j = m) {z : Fin (n + (m + 1)) → ℝ} (hz : z ∈ S.X.set)
    (hzc : z ∉ (Work.WilE7.critSet S (Fin.last m)).set) :
    Module.finrank ℝ
      ((LinearMap.ker (Work.WilE7.MainDesign.jac S z)).map
        (Work.WilE7.CoreStep.projTopLin n m)) = n + 1 := by
  classical
  -- 1. some critical minor does not vanish at `z`
  have hnot : ∃ σ : Fin (S.j + 1) → Fin (m + 1),
      eaEval S.X.c (Work.WilE7.critMinor S.X.c S.h (Fin.last m) σ) z ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hzc (by rw [Work.WilE7.critSet_set]; exact ⟨hz, hcon⟩)
  -- 2. the evaluated augmented matrix `[∂_y h ; e_last]` and its last row
  let Aug : Matrix (Fin (S.j + 1)) (Fin (m + 1)) ℝ := Matrix.of (fun a l' =>
    eaEval S.X.c (eaD S.X.c (Fin.natAdd n l')
      (Fin.lastCases (MvPolynomial.X (Sum.inl (Fin.natAdd n (Fin.last m)))) S.h a)) z)
  have hlast : ∀ l' : Fin (m + 1), Aug (Fin.last S.j) l' = if l' = Fin.last m then 1 else 0 := by
    intro l'
    show eaEval S.X.c (eaD S.X.c (Fin.natAdd n l')
      (Fin.lastCases (MvPolynomial.X (Sum.inl (Fin.natAdd n (Fin.last m)))) S.h (Fin.last S.j))) z
      = if l' = Fin.last m then 1 else 0
    rw [Fin.lastCases_last, eaEval_eaD_X_inl]
    by_cases hl : l' = Fin.last m
    · rw [hl]
      simp
    · rw [ite_eq_right hl, ite_eq_right (fun hh => hl (Fin.natAdd_injective (m + 1) n hh))]
  have hmin : ∃ σ : Fin (S.j + 1) → Fin (m + 1), (Aug.submatrix id σ).det ≠ 0 := by
    obtain ⟨σ, hσ⟩ := hnot
    refine ⟨σ, fun hdet => hσ ?_⟩
    rw [← eaEval_critMinor_eq_det S.X.c S.h z σ]
    exact hdet
  -- 3. the matrix of the Jacobian (the definition of `jac S z`) and the middle block
  let Jac : Matrix (Fin S.j) (Fin (n + (m + 1))) ℝ :=
    Matrix.of (fun a l => eaEval S.X.c (eaD S.X.c l (S.h a)) z)
  have hjac : Work.WilE7.MainDesign.jac S z = Jac.mulVecLin := rfl
  rw [hjac]
  let Mid : Matrix (Fin S.j) (Fin m) ℝ :=
    Matrix.of (fun (a : Fin S.j) (c : Fin m) => Aug (Fin.castSucc a) (Fin.castSucc c))
  have hkerA : LinearMap.ker Mid.mulVecLin = ⊥ :=
    middle_ker_bot_of_nonzero_minor Aug hlast hj hmin
  have hcol : ∀ (a : Fin S.j) (c : Fin m), Mid a c = Jac a (Fin.natAdd n (Fin.castSucc c)) := by
    intro a c
    simp only [Matrix.of_apply, Mid, Jac, Aug, Fin.lastCases_castSucc]
  -- 4. `projTopLin` is injective on `ker (jac S z)`
  have hcompker : LinearMap.ker ((Work.WilE7.CoreStep.projTopLin n m).comp
      (LinearMap.ker Jac.mulVecLin).subtype) = ⊥ :=
    ker_proj_bot_of_middle_ker_bot Jac Mid hcol hkerA
  -- 5. the projection preserves the dimension of the tangent space
  have hmap : Module.finrank ℝ ((LinearMap.ker Jac.mulVecLin).map
          (Work.WilE7.CoreStep.projTopLin n m))
      = Module.finrank ℝ ↥(LinearMap.ker Jac.mulVecLin) := by
    have h := LinearMap.finrank_range_add_finrank_ker
      ((Work.WilE7.CoreStep.projTopLin n m).comp (LinearMap.ker Jac.mulVecLin).subtype)
    rw [LinearMap.range_comp, Submodule.range_subtype] at h
    have h0 : Module.finrank ℝ ↥(((Work.WilE7.CoreStep.projTopLin n m).comp
        (LinearMap.ker Jac.mulVecLin).subtype).ker) = 0 := by
      rw [hcompker]
      simp
    rw [h0, add_zero] at h
    exact h
  -- 6. rank–nullity: the tangent space has dimension at least `n + 1`, and its `projTop`-image
  --    has dimension at most `n + 1`
  have hge : n + 1 ≤ Module.finrank ℝ ↥(LinearMap.ker Jac.mulVecLin) := by
    have h := LinearMap.finrank_range_add_finrank_ker Jac.mulVecLin
    have hle : Module.finrank ℝ (LinearMap.range Jac.mulVecLin) ≤ m := by
      calc Module.finrank ℝ (LinearMap.range Jac.mulVecLin)
          ≤ Module.finrank ℝ (Fin S.j → ℝ) := Submodule.finrank_le _
        _ = S.j := by simp
        _ = m := hj
    have hdom : Module.finrank ℝ (Fin (n + (m + 1)) → ℝ) = n + (m + 1) := by simp
    omega
  have hle' : Module.finrank ℝ ((LinearMap.ker Jac.mulVecLin).map
        (Work.WilE7.CoreStep.projTopLin n m)) ≤ n + 1 := by
    calc Module.finrank ℝ ((LinearMap.ker Jac.mulVecLin).map
            (Work.WilE7.CoreStep.projTopLin n m))
        ≤ Module.finrank ℝ (Fin (n + 1) → ℝ) := Submodule.finrank_le _
      _ = n + 1 := by simp
  omega

end Work.WilE7.CoreStep
