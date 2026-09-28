import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.Lat.detL_basis_gram

namespace Work.HP.GM

/-!
# The index formula for `detL`

`Work.HP.detL L` is the covolume of the integral lattice `L ⊆ ℤ^ι` in its own real span,
defined as the square root of the determinant of the Gram matrix of a `ℤ`-basis of `L`.

The main result of this file is the classical index–covolume relation: if `L ≤ Λ` are
integral lattices of the same rank, then

  `detL L = detL Λ * [Λ : L]`,

where `[Λ : L] = Nat.card (Λ ⧸ L)` is the index of `L` in `Λ`.

The proof picks `ℤ`-bases `bΛ` of `Λ` and `bN` of `N = L.comap Λ.subtype ≅ L` indexed by the
same finite type `Fin n`.  Writing `T` for the transition matrix expressing `bN` in `bΛ` and
`G` for the (integer) Gram matrix of `bΛ` in the standard inner product `ipForm`, the Gram
matrix of the basis of `L` is `Tᵀ G T`, whence

  `detL L = sqrt (det T ^ 2 * det G) = |det T| * detL Λ`.

Finally `|det T| = Nat.card (Λ ⧸ N)` is exactly Mathlib's `Submodule.natAbs_det_basis_change`.
-/

/-- `detL M` is the square root of the determinant of the *integer* Gram matrix of any `ℤ`-basis
of `M`, the Gram matrix being taken with respect to the standard inner product form `ipForm`. -/
lemma detL_eq_sqrt_intgram {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Submodule ℤ (ι → ℤ))
    {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Module.Basis κ ℤ M) :
    Work.HP.detL M =
      Real.sqrt ((LinearMap.BilinForm.toMatrix b (Work.HP.Lat.ipForm M)).det : ℝ) := by
  rw [Work.HP.Lat.detL_basis_gram M b]
  change Real.sqrt (Matrix.det (Work.HP.Lat.gramR M b)) = _
  rw [Work.HP.Lat.gramR_eq_toMatrix M b]
  congr 1
  exact (RingHom.map_det (Int.castRingHom ℝ) _).symm

/-- For real numbers `a`, `g`: `sqrt (a ^ 2 * g) = |a| * sqrt g`.  With Lean's convention
`Real.sqrt x = 0` for `x < 0` this holds unconditionally (and is used with no sign hypothesis
on `g`). -/
lemma sqrt_sq_mul (a g : ℝ) : Real.sqrt (a ^ 2 * g) = |a| * Real.sqrt g := by
  rw [mul_comm (a ^ 2), Real.sqrt_mul' g (sq_nonneg a), Real.sqrt_sq_eq_abs]
  ring

theorem detL_index {ι : Type} [Fintype ι] [DecidableEq ι] (Λ L : Submodule ℤ (ι → ℤ)) (h : L ≤ Λ)
    (hfin : Module.finrank ℤ L = Module.finrank ℤ Λ) :
    Work.HP.detL L = Work.HP.detL Λ * (Nat.card (Λ ⧸ L.comap Λ.subtype) : ℝ) := by
  classical
  -- `N` is `L` viewed as a submodule of `Λ`.
  let N : Submodule ℤ Λ := L.comap Λ.subtype
  let he : N ≃ₗ[ℤ] L := Submodule.comapSubtypeEquivOfLe h
  have hfrN : Module.finrank ℤ N = Module.finrank ℤ L := he.finrank_eq
  -- bases of `Λ` and of `N` over a common index type.
  obtain ⟨nΛ, bΛ⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) Λ
  obtain ⟨nN, hbN⟩ := Submodule.basisOfPid bΛ N
  have hΛ : Module.finrank ℤ Λ = nΛ := by
    rw [Module.finrank_eq_card_basis bΛ, Fintype.card_fin]
  have hN : Module.finrank ℤ N = nN := by
    rw [Module.finrank_eq_card_basis hbN, Fintype.card_fin]
  have hn : nN = nΛ := by rw [← hN, hfrN, hfin, hΛ]
  let bN : Module.Basis (Fin nΛ) ℤ N := hbN.reindex (finCongr hn)
  -- a basis of `L` obtained from the basis of `N` along the identification `N ≃ L`.
  let bL : Module.Basis (Fin nΛ) ℤ L := bN.map he
  -- the transition matrix, the two Gram matrices.
  let BΛ : LinearMap.BilinForm ℤ Λ := Work.HP.Lat.ipForm Λ
  let G : Matrix (Fin nΛ) (Fin nΛ) ℤ := LinearMap.BilinForm.toMatrix bΛ BΛ
  let T : Matrix (Fin nΛ) (Fin nΛ) ℤ := LinearMap.toMatrix bN bΛ N.subtype
  let Mv : Matrix (Fin nΛ) (Fin nΛ) ℤ :=
    LinearMap.BilinForm.toMatrix bN (BΛ.comp N.subtype N.subtype)
  -- the coordinates of the basis of `L` agree with those of the basis of `N` inside `Λ`.
  have hcol : (fun i => ((bL i : L) : ι → ℤ)) = (fun i => ((N.subtype (bN i) : Λ) : ι → ℤ)) := by
    funext i
    simp only [Module.Basis.map_apply, bL]
    exact Submodule.comapSubtypeEquivOfLe_apply_coe h (bN i)
  -- the Gram matrix of the basis of `L` is the Gram matrix of `bN` for the restricted form.
  have hgram : LinearMap.BilinForm.toMatrix bL (Work.HP.Lat.ipForm L) = Mv := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.comp_apply,
      Work.HP.Lat.ipForm, LinearMap.mk₂_apply, Work.HP.Lat.ip, Mv, BΛ]
    rw [show ((bL i : L) : ι → ℤ) = ((N.subtype (bN i) : Λ) : ι → ℤ) from congrFun hcol i,
      show ((bL j : L) : ι → ℤ) = ((N.subtype (bN j) : Λ) : ι → ℤ) from congrFun hcol j]
  -- the change-of-basis formula for the bilinear form.
  have hMv : Mv = T.transpose * G * T := by
    have hc := LinearMap.BilinForm.toMatrix_comp (b := bΛ) (c := bN) BΛ N.subtype N.subtype
    simpa only [Mv, T, G, BΛ] using hc
  -- the index is the absolute value of the determinant of the transition matrix.
  have hT : T = bΛ.toMatrix (Subtype.val ∘ ⇑bN) := by
    ext i j
    simp [T, LinearMap.toMatrix_apply, Module.Basis.toMatrix_apply]
  have hidx : (T.det).natAbs = Nat.card (Λ ⧸ N) := by
    rw [hT]
    exact Submodule.natAbs_det_basis_change bΛ N bN
  -- determinant of the Gram matrix of the basis of `L`, over `ℝ`.
  have hdetMv : (Mv.det : ℝ) = (T.det : ℝ) ^ 2 * (G.det : ℝ) := by
    have hd : Mv.det = T.det ^ 2 * G.det := by
      rw [hMv, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      ring
    rw [hd]
    push_cast
    ring
  have hcast : |((T.det : ℤ) : ℝ)| = (Nat.card (Λ ⧸ N) : ℝ) := by
    have h1 : |((T.det : ℤ) : ℝ)| = (T.det.natAbs : ℝ) := by simp [Nat.cast_natAbs]
    rw [h1, show T.det.natAbs = Nat.card (Λ ⧸ N) from hidx]
  have hL : Work.HP.detL L =
      Real.sqrt ((Mv.det : ℝ)) := by
    rw [detL_eq_sqrt_intgram L bL, hgram]
  have hΛ' : Work.HP.detL Λ = Real.sqrt ((G.det : ℝ)) :=
    detL_eq_sqrt_intgram Λ bΛ
  calc Work.HP.detL L = Real.sqrt ((Mv.det : ℝ)) := hL
    _ = Real.sqrt (((T.det : ℝ) ^ 2) * (G.det : ℝ)) := by rw [hdetMv]
    _ = |((T.det : ℤ) : ℝ)| * Real.sqrt ((G.det : ℝ)) := sqrt_sq_mul _ _
    _ = (Nat.card (Λ ⧸ N) : ℝ) * Work.HP.detL Λ := by rw [hcast, ← hΛ']
    _ = Work.HP.detL Λ * (Nat.card (Λ ⧸ N) : ℝ) := by ring

end Work.HP.GM
