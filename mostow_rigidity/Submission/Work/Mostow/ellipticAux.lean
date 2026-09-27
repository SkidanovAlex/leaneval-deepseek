import Mathlib
import Submission.Work.Mostow.ellipticDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.HaarBoost
import Submission.Work.Mostow.blkMap_linBlk
import Submission.Work.Mostow.fix_zero_is_euclidean

/-!
# Auxiliary lemmas for the elliptic normal form

* casts along equalities of dimensions;
* `po_ext` (faithfulness) and `hdist`-preservation of linear isometries;
* the action of `blk k m 1 R` on the chart (`blk_smul_linBlk`), deduced from the Fermi
  linearisation `blkMap_linBlk`, the isometry property `hdist_linBlk` and the defining
  `if` of `blk`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## Casts along equalities of dimensions -/

section Cast

variable {a b : ℕ}

lemma cast_smul_po (e : a = b) (X : PO a 1) (u : E a) :
    ((e ▸ X : PO b 1) • (e ▸ u : E b)) = (e ▸ (X • u) : E b) := by
  cases e; rfl

lemma cast_mul_po (e : a = b) (X Y : PO a 1) :
    (e ▸ (X * Y) : PO b 1) = (e ▸ X) * (e ▸ Y) := by cases e; rfl

lemma cast_inv_po (e : a = b) (X : PO a 1) : (e ▸ X⁻¹ : PO b 1) = (e ▸ X)⁻¹ := by cases e; rfl

lemma cast_hlift (e : a = b) (u : E a) :
    (e ▸ (hlift u) : Fin b ⊕ Fin 1 → ℝ) = hlift (e ▸ u : E b) := by cases e; rfl

lemma cast_fin_valX (a b : ℕ) (e : a = b) (i : Fin a) :
    ((finCongr e i : Fin b) : ℕ) = (i : ℕ) := by
  cases e; rfl

lemma cast_applyX (a b : ℕ) (e : a = b) (w : E a) (i : Fin b) :
    WithLp.ofLp (e ▸ w : E b) i = WithLp.ofLp w (finCongr e.symm i) := by
  cases e; rfl

lemma cast_applyX' (a b : ℕ) (e : a = b) (u : E b) (j : Fin a) :
    WithLp.ofLp (e.symm ▸ u : E a) j = WithLp.ofLp u (finCongr e j) := by
  cases e; rfl

lemma cast_symm_cast (e : a = b) (u : E b) : (e ▸ (e.symm ▸ u) : E b) = u := by
  cases e; rfl

lemma cast_symm_cast_po (e : a = b) (X : PO b 1) :
    (e ▸ (e.symm ▸ X) : PO b 1) = X := by cases e; rfl

end Cast

/-! ## Faithfulness and isometries -/

/-- Two elements of `PO n 1` acting identically on the chart are equal. -/
lemma po_ext (hA : POBasic n) {g₁ g₂ : PO n 1} (h : ∀ u : E n, g₁ • u = g₂ • u) : g₁ = g₂ := by
  have h1 : ∀ u : E n, (g₁⁻¹ * g₂) • u = u := by
    intro u
    rw [hA.mul_smul, ← h u, ← hA.mul_smul, inv_mul_cancel, hA.one_smul]
  have h2 : g₁⁻¹ * g₂ = 1 := hA.faithful _ h1
  calc g₁ = g₁ * (g₁⁻¹ * g₂) := by rw [h2, mul_one]
    _ = (g₁ * g₁⁻¹) * g₂ := by rw [mul_assoc]
    _ = g₂ := by rw [mul_inv_cancel, one_mul]

/-- A linear isometry equivalence preserves `hdist`. -/
lemma hdist_linearIsometryEquiv (φ : E n ≃ₗᵢ[ℝ] E n) (u v : E n) :
    hdist (φ u) (φ v) = hdist u v := by
  simp only [hdist, tpart, φ.norm_map u, φ.norm_map v, φ.inner_map_map u v]


/-! ## Coordinates of `linBlk` and its metric properties (local proofs) -/

/-- `linBlk` preserves norms. -/
lemma norm_linBlk (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m)) :
    ‖linBlk k m R u‖ = ‖u‖ := by
  have hsq : ‖linBlk k m R u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [Hyper.norm_sq_eq_sum, Hyper.norm_sq_eq_sum,
      Fin.sum_univ_add (f := fun i : Fin (k + m) =>
        (linBlk k m R u).ofLp i * (linBlk k m R u).ofLp i),
      Fin.sum_univ_add (f := fun i : Fin (k + m) => u.ofLp i * u.ofLp i)]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by
        simp only [linBlk, WithLp.ofLp_toLp, Fin.append_left]
    · have h1 : (∑ j : Fin m, (linBlk k m R u).ofLp (Fin.natAdd k j)
              * (linBlk k m R u).ofLp (Fin.natAdd k j))
            = ∑ j : Fin m,
                (R (WithLp.toLp 2 (fun j' => u.ofLp (Fin.natAdd k j')))).ofLp j
                  * (R (WithLp.toLp 2 (fun j' => u.ofLp (Fin.natAdd k j')))).ofLp j :=
          Finset.sum_congr rfl fun j _ => by
            simp only [linBlk, WithLp.ofLp_toLp, Fin.append_right]
      rw [h1,
        ← Hyper.norm_sq_eq_sum (R (WithLp.toLp 2 (fun j' => u.ofLp (Fin.natAdd k j')))),
        R.norm_map,
        Hyper.norm_sq_eq_sum (WithLp.toLp 2 (fun j' => u.ofLp (Fin.natAdd k j')))]
  rw [← Real.sqrt_sq (norm_nonneg (linBlk k m R u)), ← Real.sqrt_sq (norm_nonneg u), hsq]

/-- `linBlk` preserves inner products. -/
lemma inner_linBlk (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u v : E (k + m)) :
    inner ℝ (linBlk k m R u) (linBlk k m R v) = inner ℝ u v := by
  rw [Hyper.inner_eq_sum, Hyper.inner_eq_sum,
    Fin.sum_univ_add (f := fun i : Fin (k + m) =>
      (linBlk k m R u).ofLp i * (linBlk k m R v).ofLp i),
    Fin.sum_univ_add (f := fun i : Fin (k + m) => u.ofLp i * v.ofLp i)]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by
      simp only [linBlk, WithLp.ofLp_toLp, Fin.append_left]
  · have h1 : (∑ j : Fin m, (linBlk k m R u).ofLp (Fin.natAdd k j)
            * (linBlk k m R v).ofLp (Fin.natAdd k j))
          = ∑ j : Fin m,
              (R (WithLp.toLp 2 (fun j' => u.ofLp (Fin.natAdd k j')))).ofLp j
                * (R (WithLp.toLp 2 (fun j' => v.ofLp (Fin.natAdd k j')))).ofLp j :=
        Finset.sum_congr rfl fun j _ => by
          simp only [linBlk, WithLp.ofLp_toLp, Fin.append_right]
    rw [h1,
      ← Hyper.inner_eq_sum (R (WithLp.toLp 2 (fun j' => u.ofLp (Fin.natAdd k j'))))
        (R (WithLp.toLp 2 (fun j' => v.ofLp (Fin.natAdd k j')))),
      R.inner_map_map,
      Hyper.inner_eq_sum (WithLp.toLp 2 (fun j' => u.ofLp (Fin.natAdd k j')))
        (WithLp.toLp 2 (fun j' => v.ofLp (Fin.natAdd k j')))]

/-- `linBlk` is an `hdist`-isometry. -/
lemma hdist_linBlk_chart (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u v : E (k + m)) :
    hdist (linBlk k m R u) (linBlk k m R v) = hdist u v := by
  simp only [hdist, tpart, norm_linBlk, inner_linBlk]

/-- The value-split block map is the cast of the split block map. -/
lemma vblk_cast_linBlk_chart (k : ℕ) {n : ℕ} (hk : k ≤ n) (e : k + (n - k) = n)
    (R : E (n - k) ≃ₗᵢ[ℝ] E (n - k)) (u : E n) :
    (e ▸ linBlk k (n - k) R (e.symm ▸ u) : E n) = vblk k hk R u := by
  apply WithLp.ofLp_injective
  funext i
  rw [cast_applyX (k + (n - k)) n e, vblk]
  simp only [WithLp.ofLp_toLp]
  split_ifs with hi
  · have hidx : (finCongr e.symm i : Fin (k + (n - k)))
        = Fin.castAdd (n - k) ⟨(i : ℕ), hi⟩ := by
      apply Fin.ext
      simp [cast_fin_valX n (k + (n - k)) e.symm]
    have hidx2 : finCongr e (Fin.castAdd (n - k) ⟨(i : ℕ), hi⟩) = i := by
      apply Fin.ext
      simp [cast_fin_valX (k + (n - k)) n e]
    rw [hidx]
    simp only [linBlk, WithLp.ofLp_toLp, Fin.append_left]
    rw [cast_applyX' (k + (n - k)) n e, hidx2]
  · have hi' : k ≤ (i : ℕ) := Nat.le_of_not_lt hi
    have hidx : (finCongr e.symm i : Fin (k + (n - k)))
        = Fin.natAdd k ⟨(i : ℕ) - k, by omega⟩ := by
      apply Fin.ext
      simp only [cast_fin_valX n (k + (n - k)) e.symm, Fin.val_natAdd]
      omega
    have harg : (fun j' : Fin (n - k) => (e.symm ▸ u).ofLp (Fin.natAdd k j'))
        = fun j : Fin (n - k) => u.ofLp ⟨k + (j : ℕ), by omega⟩ := by
      funext j'
      rw [cast_applyX' (k + (n - k)) n e]
      have hidx3 : finCongr e (Fin.natAdd k j') = ⟨k + (j' : ℕ), by omega⟩ := by
        apply Fin.ext
        rw [cast_fin_valX (k + (n - k)) n e, Fin.val_natAdd]
      rw [hidx3]
    rw [hidx]
    simp only [linBlk, WithLp.ofLp_toLp, Fin.append_right]
    rw [harg]

/-! ## The action of `blk k m 1 R` -/

/-- `blk k m 1 R` acts on the chart as the linear block map `linBlk k m R`. -/
lemma blk_smul_linBlk (k m : ℕ) (hAk : POActionProp k) (hA : POActionProp (k + m))
    (hI : HypIsometryProp (k + m)) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m)) :
    (blk k m 1 R : PO (k + m) 1) • u = linBlk k m R u := by
  have hAb := POBasic.ofProp hA
  have hIb := HypIsoData.ofProp hI
  -- an element acting as `linBlk`
  obtain ⟨G, hG⟩ := hIb.surj_isom (linBlk k m R) (fun u v => hdist_linBlk_chart k m R u v)
  have hex : ∃ g : PO (k + m) 1, ∀ u : E (k + m), g • u = blkMap k m 1 R u :=
    ⟨G, fun u => by rw [← hG u, ← blkMap_linBlk k m hAk R u]⟩
  have hblk : blk k m 1 R = hex.choose := by
    rw [blk]
    exact dif_pos hex
  have hchoose : ∀ u : E (k + m), hex.choose • u = blkMap k m 1 R u :=
    Classical.choose_spec hex
  have hEq : blk k m 1 R = G := by
    refine po_ext hAb (fun u => ?_)
    rw [hblk, hchoose u, blkMap_linBlk k m hAk R u, hG u]
  rw [hEq, hG u]

end

end Work.Mostow
