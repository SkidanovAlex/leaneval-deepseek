/-
  WilE9 / Sharp — the fibre Jacobian of the pulled-back system is invertible.

  `pb_det_ne_zero` is the `hP`-input of the E9 assembly (BNZ §3): the effective-smoothness of
  the stratum (`EffStratum.Good`) gives the invertibility of the Jacobian `∂h / ∂(τ, aux)` of the
  stratum's equations, and the pulled-back system `pbF` — the equations `τ - s u`,
  `y i - x i * w i`, `y i ^ 2 + w i ^ 2 - 1`, `τ ^ 2 + u ^ 2 - 1`, `h` — must have invertible
  fibre Jacobian there.

  The proof is an explicit elimination of the linear system `M v = 0`:

  * the two rows `y i = x i * w i` and `y i ^ 2 + w i ^ 2 = 1` force `v (fY i) = v (fW i) = 0`,
    because `y i = x i * w i` turns their combination into `2 * w i * (x i ^ 2 + 1) * v (fW i) = 0`
    and `w i ≠ 0`;
  * the stratum rows (`Mmat_mulVec_hRow`), once the `y`-coordinates are known to vanish, are
    exactly the matrix `∂h / ∂(τ, aux)`, which is invertible by hypothesis; hence
    `v (fT) = v (fA b) = 0`;
  * the rows `τ - s u` and `τ ^ 2 + u ^ 2 - 1` then force `v (fU) = v (fS) = 0` since `u ≠ 0`;
  * `PbDet.eq_zero_of_qpb` turns the vanishing on the six families of fibre coordinates into
    `v = 0`.

  The row vectors of `M` are supplied by `PbDet.RowEntries` (the four algebraic rows) and
  `PbDet.HRowEntry` (the stratum rows).
-/
import Mathlib
import Submission.Work.WilE9.Sharp.PbDetDefs
import Submission.Work.WilE9.Sharp.PbDet.RowEntries
import Submission.Work.WilE9.Sharp.PbDet.HRowEntry
import Submission.Work.WilE9.Sharp.PbDet.eq_zero_of_qpb

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-! ## Sums over the support of a vector -/

private lemma dotProduct_eq_of_support {N : ℕ} (x u : Fin N → ℝ) (s : Finset (Fin N))
    (h : ∀ l, l ∉ s → x l = 0) : x ⬝ᵥ u = ∑ l ∈ s, x l * u l := by
  rw [dotProduct]
  rw [← Finset.sum_subset (Finset.subset_univ s) (fun x _ hx => by rw [h x hx, zero_mul])]

private lemma mulVec_apply_eq_of_support {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (u : Fin N → ℝ)
    (j : Fin N) (s : Finset (Fin N)) (h : ∀ l, l ∉ s → A j l = 0) :
    A.mulVec u j = ∑ l ∈ s, A j l * u l := by
  rw [Matrix.mulVec_apply, Matrix.row]
  exact dotProduct_eq_of_support _ _ s h

/-! ## The row vectors of the fibre Jacobian -/

section RowVectors

variable {n m r : ℕ}

private lemma Mmat_mulVec_fY (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (z : Fin (Npb n m) → ℝ)
    (u : Fin (qpb n m) → ℝ) (i : Fin n) :
    (Mmat n m r c h z).mulVec u (fY n m i) = u (fY n m i) - z (pbX n m i) * u (fW n m i) := by
  have hne : fY n m i ≠ fW n m i := fY_ne_fW i
  have hrow := Mmat_row_fY c h z i
  rw [mulVec_apply_eq_of_support (Mmat n m r c h z) u (fY n m i)
    ({fY n m i, fW n m i} : Finset (Fin (qpb n m))) (by
      intro l hl
      rw [hrow l]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rw [if_neg (by tauto), if_neg (by tauto)])]
  rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
  have h1 : Mmat n m r c h z (fY n m i) (fY n m i) = 1 := by rw [hrow]; simp
  have h2 : Mmat n m r c h z (fY n m i) (fW n m i) = -z (pbX n m i) := by
    rw [hrow, if_neg (Ne.symm hne), if_pos rfl]
  rw [h1, h2]; ring

private lemma Mmat_mulVec_fW (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (z : Fin (Npb n m) → ℝ)
    (u : Fin (qpb n m) → ℝ) (i : Fin n) :
    (Mmat n m r c h z).mulVec u (fW n m i) =
      2 * z (pbY n m i) * u (fY n m i) + 2 * z (pbW n m i) * u (fW n m i) := by
  have hne : fY n m i ≠ fW n m i := fY_ne_fW i
  have hrow := Mmat_row_fW c h z i
  rw [mulVec_apply_eq_of_support (Mmat n m r c h z) u (fW n m i)
    ({fY n m i, fW n m i} : Finset (Fin (qpb n m))) (by
      intro l hl
      rw [hrow l]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rw [if_neg (by tauto), if_neg (by tauto)])]
  rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
  have h1 : Mmat n m r c h z (fW n m i) (fY n m i) = 2 * z (pbY n m i) := by
    rw [hrow, if_pos rfl]
  have h2 : Mmat n m r c h z (fW n m i) (fW n m i) = 2 * z (pbW n m i) := by
    rw [hrow, if_neg (Ne.symm hne), if_pos rfl]
  rw [h1, h2]

private lemma Mmat_mulVec_fT (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (z : Fin (Npb n m) → ℝ)
    (u : Fin (qpb n m) → ℝ) :
    (Mmat n m r c h z).mulVec u (fT n m) =
      2 * z (pbT n m) * u (fT n m) + 2 * z (pbU n m) * u (fU n m) := by
  have hne : fT n m ≠ fU n m := fT_ne_fU
  have hrow := Mmat_row_fT c h z
  rw [mulVec_apply_eq_of_support (Mmat n m r c h z) u (fT n m)
    ({fT n m, fU n m} : Finset (Fin (qpb n m))) (by
      intro l hl
      rw [hrow l]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rw [if_neg (by tauto), if_neg (by tauto)])]
  rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
  have h1 : Mmat n m r c h z (fT n m) (fT n m) = 2 * z (pbT n m) := by
    rw [hrow, if_pos rfl]
  have h2 : Mmat n m r c h z (fT n m) (fU n m) = 2 * z (pbU n m) := by
    rw [hrow, if_neg (Ne.symm hne), if_pos rfl]
  rw [h1, h2]

private lemma Mmat_mulVec_fS (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (z : Fin (Npb n m) → ℝ)
    (u : Fin (qpb n m) → ℝ) :
    (Mmat n m r c h z).mulVec u (fS n m) =
      -z (pbU n m) * u (fS n m) + u (fT n m) - z (pbS n m) * u (fU n m) := by
  have h1ne : fS n m ≠ fT n m := fS_ne_fT
  have h2ne : fS n m ≠ fU n m := fS_ne_fU
  have h3ne : fT n m ≠ fU n m := fT_ne_fU
  have hrow := Mmat_row_fS c h z
  rw [mulVec_apply_eq_of_support (Mmat n m r c h z) u (fS n m)
    ({fS n m, fT n m, fU n m} : Finset (Fin (qpb n m))) (by
      intro l hl
      rw [hrow l]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rw [if_neg (by tauto), if_neg (by tauto), if_neg (by tauto)])]
  rw [Finset.sum_insert (by simp [h1ne, h2ne]), Finset.sum_insert (by simp [h3ne]),
    Finset.sum_singleton]
  have ha : Mmat n m r c h z (fS n m) (fS n m) = -z (pbU n m) := by
    rw [hrow, if_pos rfl]
  have hb : Mmat n m r c h z (fS n m) (fT n m) = 1 := by
    rw [hrow, if_neg (Ne.symm h1ne), if_pos rfl]
  have hc : Mmat n m r c h z (fS n m) (fU n m) = -z (pbS n m) := by
    rw [hrow, if_neg (Ne.symm h2ne), if_neg (Ne.symm h3ne), if_pos rfl]
  rw [ha, hb, hc]; ring

end RowVectors

/-! ## The coordinates of `Fin.append x₀ y₀` in the two systems -/

private lemma append_pbX {n m : ℕ} (x₀ : Fin n → ℝ) (y₀ : Fin (qpb n m) → ℝ) (i : Fin n) :
    (Fin.append x₀ y₀) (pbX n m i) = x₀ i := by
  show (Fin.append x₀ y₀) (Fin.castAdd (qpb n m) i) = x₀ i
  rw [Fin.append_left]

private lemma append_pbY {n m : ℕ} (x₀ : Fin n → ℝ) (y₀ : Fin (qpb n m) → ℝ) (i : Fin n) :
    (Fin.append x₀ y₀) (pbY n m i) = y₀ (fY n m i) := by
  have h : pbY n m i = Fin.natAdd n (fY n m i) := by
    apply Fin.ext; simp only [Fin.natAdd, pbY, fY]; omega
  rw [h, Fin.append_right]

private lemma append_pbW {n m : ℕ} (x₀ : Fin n → ℝ) (y₀ : Fin (qpb n m) → ℝ) (i : Fin n) :
    (Fin.append x₀ y₀) (pbW n m i) = y₀ (fW n m i) := by
  have h : pbW n m i = Fin.natAdd n (fW n m i) := by
    apply Fin.ext; simp only [Fin.natAdd, pbW, fW]; omega
  rw [h, Fin.append_right]

private lemma append_pbU {n m : ℕ} (x₀ : Fin n → ℝ) (y₀ : Fin (qpb n m) → ℝ) :
    (Fin.append x₀ y₀) (pbU n m) = y₀ (fU n m) := by
  have h : pbU n m = Fin.natAdd n (fU n m) := by
    apply Fin.ext; simp only [Fin.natAdd, pbU, fU]; omega
  rw [h, Fin.append_right]

/-! ## The kernel of the fibre Jacobian is trivial -/

theorem Mmat_det_ne_zero {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (x₀ : Fin n → ℝ) (z : Fin (Npb n m) → ℝ)
    (hzy : ∀ i : Fin n, z (pbY n m i) = z (pbX n m i) * z (pbW n m i))
    (hzw : ∀ i : Fin n, z (pbW n m i) ≠ 0)
    (hzu : z (pbU n m) ≠ 0)
    (hP : (Hmat n m r c h z).det ≠ 0) :
    (Mmat n m r c h z).det ≠ 0 := by
  have hHinj : Function.Injective (Hmat n m r c h z).mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hP
  have hker : ∀ u : Fin (qpb n m) → ℝ, (Mmat n m r c h z).mulVec u = 0 → u = 0 := by
    intro u hu
    have hrow : ∀ j : Fin (qpb n m), (Mmat n m r c h z).mulVec u j = 0 := by
      intro j; rw [hu]; rfl
    -- the `w`-coordinates vanish
    have hw0 : ∀ i : Fin n, u (fW n m i) = 0 := by
      intro i
      have h1 : u (fY n m i) - z (pbX n m i) * u (fW n m i) = 0 := by
        rw [← Mmat_mulVec_fY]; exact hrow (fY n m i)
      have h2 : 2 * z (pbY n m i) * u (fY n m i) + 2 * z (pbW n m i) * u (fW n m i) = 0 := by
        rw [← Mmat_mulVec_fW]; exact hrow (fW n m i)
      have hsub : u (fY n m i) = z (pbX n m i) * u (fW n m i) := sub_eq_zero.mp h1
      have h3 : (2 * z (pbW n m i) * (z (pbX n m i) ^ 2 + 1)) * u (fW n m i) = 0 := by
        rw [hsub, hzy i] at h2
        rw [← h2]; ring
      have hcoef : 2 * z (pbW n m i) * (z (pbX n m i) ^ 2 + 1) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero (hzw i)) (by positivity)
      exact (mul_eq_zero.mp h3).resolve_left hcoef
    -- the `y`-coordinates vanish
    have hy0 : ∀ i : Fin n, u (fY n m i) = 0 := by
      intro i
      have h1 : u (fY n m i) - z (pbX n m i) * u (fW n m i) = 0 := by
        rw [← Mmat_mulVec_fY]; exact hrow (fY n m i)
      rw [hw0 i, mul_zero, sub_zero] at h1
      exact h1
    -- the stratum rows become the `(τ, aux)`-system
    have hH0 : (Hmat n m r c h z).mulVec (wVec u) = 0 := by
      funext a
      rw [← Mmat_mulVec_hRow c h z u hy0 a]
      exact hrow (hRow n m a)
    have hwv : wVec u = 0 := hHinj (by rw [hH0, Matrix.mulVec_zero])
    have huT : u (fT n m) = 0 := by
      have hh := congrFun hwv (0 : Fin (1 + m))
      rw [wVec_apply] at hh
      simpa using hh
    have huA : ∀ b : Fin m, u (fA n m b) = 0 := by
      intro b
      have hh := congrFun hwv (⟨b.val + 1, by have := b.isLt; omega⟩ : Fin (1 + m))
      rw [wVec_apply] at hh
      have hcl : hColIdx n m (⟨b.val + 1, by have := b.isLt; omega⟩ : Fin (1 + m)) =
          fA n m b := by
        rw [hColIdx_of_ne_zero (by simp)]
        congr 1
      rwa [hcl] at hh
    -- the `u`- and `s`-coordinates vanish
    have hT : 2 * z (pbT n m) * u (fT n m) + 2 * z (pbU n m) * u (fU n m) = 0 := by
      rw [← Mmat_mulVec_fT]; exact hrow (fT n m)
    have huU : u (fU n m) = 0 := by
      rw [huT, mul_zero, zero_add] at hT
      exact (mul_eq_zero.mp hT).resolve_left (mul_ne_zero two_ne_zero hzu)
    have hS : -z (pbU n m) * u (fS n m) + u (fT n m) - z (pbS n m) * u (fU n m) = 0 := by
      rw [← Mmat_mulVec_fS]; exact hrow (fS n m)
    have huS : u (fS n m) = 0 := by
      rw [huT, huU, mul_zero, sub_zero, add_zero] at hS
      exact (mul_eq_zero.mp hS).resolve_left (neg_ne_zero.mpr hzu)
    exact PbDet.eq_zero_of_qpb u huS hy0 hw0 huT huU huA
  have hinj : Function.Injective (Mmat n m r c h z).mulVec := by
    intro v w hvw
    have h1 : v - w = 0 := hker (v - w) (by rw [Matrix.mulVec_sub, hvw, sub_self])
    rwa [sub_eq_zero] at h1
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp ((Matrix.mulVec_injective_iff_isUnit).mp hinj))

/-! ## The statement -/

theorem pb_det_ne_zero {n m r : ℕ} (c : WilkiesDesign.E.EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → WilkiesDesign.E.EAPoly (n + (1 + m)) r) (x₀ : Fin n → ℝ)
    (y₀ : Fin (Work.WilE9.Sharp.qpb n m) → ℝ)
    (hy : ∀ i : Fin n, y₀ (Work.WilE9.Sharp.fY n m i) = x₀ i * y₀ (Work.WilE9.Sharp.fW n m i))
    (hw : ∀ i : Fin n, y₀ (Work.WilE9.Sharp.fW n m i) ≠ 0)
    (hu : y₀ (Work.WilE9.Sharp.fU n m) ≠ 0)
    (hP : (Matrix.of fun (a : Fin (1 + m)) (l : Fin (1 + m)) =>
        WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Fin.natAdd n l) (h a))
          (Work.WilE9.Sharp.pbStrat (Fin.append x₀ y₀))).det ≠ 0) :
    (Matrix.of fun (j : Fin (Work.WilE9.Sharp.qpb n m)) (l : Fin (Work.WilE9.Sharp.qpb n m)) =>
        WilkiesDesign.E.eaEval (Work.WilE9.Sharp.pbChain c)
          (WilkiesDesign.E.eaD (Work.WilE9.Sharp.pbChain c) (Fin.natAdd n l)
            (Work.WilE9.Sharp.pbF n m r h j)) (Fin.append x₀ y₀)).det ≠ 0 := by
  refine Mmat_det_ne_zero c h x₀ (Fin.append x₀ y₀) ?_ ?_ ?_ ?_
  · intro i
    rw [append_pbY, append_pbX, append_pbW]
    exact hy i
  · intro i
    rw [append_pbW]
    exact hw i
  · rw [append_pbU]
    exact hu
  · simp only [Hmat]
    exact hP

end Work.WilE9.Sharp
