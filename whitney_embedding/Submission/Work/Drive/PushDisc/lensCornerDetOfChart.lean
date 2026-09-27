import Mathlib
import Submission.Work.Drive.PushDisc.lensCornerSign
import Submission.Work.Drive.PushDisc.signOfCoreDerivative_of_immersion

/-!
# `Work.Drive.PushDisc.lensCornerDetOfChart`

The determinant of the framing chart's corner frame (the `L1` of the lens assembly).

The model space is `Mdl k = ℝ × ℝ × E^k × E^k` with coordinates `(x,y,u,v)` (`lcsX`, `lcsY`,
`lcsUp`, `lcsVp`), `PP k = ℝ × E^k` is the block `(x,u)`, `Xu`/`Yv` are the two projections of the
model space onto `PP k` and `pairZ : Mdl k ≃ (PP k) × (PP k)` is the pairing `(x,y,u,v) ↦ ((x,u),(y,v))`.

For a linear map `L : PP k →ₗ Mdl k` (the jet of the finger over the `(x,v)`-plane) and a scalar `c`
the statement computes the determinant of the frame

`F = [e_x, c • (e_x - L (1,0)), L (0, e_l), ιu_l]`

in the coordinates `lcsT k` of the model space:

    frameDet (2+k+k) (lcsT k) F = -c * det (Yv ∘ L).

The proof is a determinant computation.  Writing `E := lcsSum F ∘ₗ lcsLin k` for the endomorphism
the frame induces, and conjugating by `pairZ`, the composite becomes the **block-triangular**
endomorphism

    Ê (p, q) = (p + B q, A q),      A = (Yv ∘ L) ∘ T,   T (y,v) = (-c*y, v),

whose determinant is `det A = det (Yv ∘ L) * det T = det (Yv ∘ L) * (-c)`:

* `lcs_frameDet_eq` (`lensCornerSign.lean`) — the frame determinant *is* the determinant of
  `lcsSum F ∘ₗ lcsLin k`;
* `lcsSum_cornerFrame` (`lensCornerSign.lean`) — the value of that endomorphism on a vector;
* `det_prod_block` (`det_pairZ_inc_coprod_graph.lean`) — the determinant of a block-triangular
  endomorphism of a product `X × Y`;
* `lcs_det_one_add_of_comp_self_eq_zero`, `LinearMap.det_conj`, `LinearMap.det_comp`.

## Main result

* `lensCornerDetOfChart` — the target identity.
-/

namespace Work.Drive.PushDisc

noncomputable section

variable {k : ℕ}

/-! ## §1 The auxiliary endomorphisms -/

/-- The `u`-inclusion, evaluated: `uPart k v = (0,0,v,0)`. -/
theorem lens_uPart_apply (k : ℕ) (v : lcsE k) : uPart k v = (0, 0, v, 0) := rfl

/-! ## §2 The map `T (y,v) = (-c y, v)` and its determinant -/

/-- The endomorphism `T : PP k → PP k`, `(y,v) ↦ (-c y, v)`, in the shape needed for
`det_prod_block`. -/
noncomputable def lensT (k : ℕ) (c : ℝ) : PP k →ₗ[ℝ] PP k :=
  (((LinearMap.mulLeft ℝ (-c)).comp (LinearMap.fst ℝ ℝ (lcsE k))) +
    ((0 : lcsE k →ₗ[ℝ] ℝ).comp (LinearMap.snd ℝ ℝ (lcsE k)))).prod
      ((LinearMap.id : lcsE k →ₗ[ℝ] lcsE k).comp (LinearMap.snd ℝ ℝ (lcsE k)))

@[simp] theorem lensT_apply (k : ℕ) (c : ℝ) (ζ : PP k) : lensT k c ζ = (-c * ζ.1, ζ.2) := by
  rcases ζ with ⟨y, v⟩
  simp [lensT, LinearMap.prod_apply, LinearMap.mulLeft_apply]

/-- `det (lensT k c) = -c`. -/
theorem lensT_det (k : ℕ) (c : ℝ) : LinearMap.det (lensT k c) = -c := by
  rw [lensT, det_prod_block, LinearMap.det_mulLeft, LinearMap.det_id, mul_one]

/-! ## §3 The frame and the endomorphism it induces -/

/-- The corner frame of the target statement. -/
noncomputable abbrev lensF (k : ℕ) (L : PP k →ₗ[ℝ] lcsM k) (c : ℝ) : Fin (2 + k + k) → lcsM k :=
  Fin.append (Fin.append ![(1, 0, 0, 0),
      c • ((1, 0, 0, 0) - L ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))))]
    (fun l : Fin k => L ((0 : ℝ), EuclideanSpace.single l 1))) (iotaU k)

/-- The endomorphism of the model space induced by the corner frame. -/
noncomputable def lensE (k : ℕ) (L : PP k →ₗ[ℝ] lcsM k) (c : ℝ) : lcsM k →ₗ[ℝ] lcsM k :=
  (lcsX k).smulRight ((1, 0, 0, 0) : lcsM k)
    + (((c : ℝ) • (lcsY k)).smulRight ((1, 0, 0, 0) : lcsM k))
    - (((c : ℝ) • (lcsY k)).smulRight (L ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k)))))
    + (L.comp (((0 : lcsM k →ₗ[ℝ] ℝ)).prod (lcsVp k)))
    + ((uPart k).comp (lcsUp k))

@[simp] theorem lensE_apply (k : ℕ) (L : PP k →ₗ[ℝ] lcsM k) (c : ℝ) (ξ : lcsM k) :
    lensE k L c ξ = ξ.1 • (1, 0, 0, 0) + (c * ξ.2.1) • ((1, 0, 0, 0) : lcsM k)
      - (c * ξ.2.1) • L (1, 0) + L (0, ξ.2.2.2) + (0, 0, ξ.2.2.1, 0) := by
  simp [lensE, LinearMap.prod_apply, lens_uPart_apply]

/-- Splitting `L` on the block `PP k`: `L (s, w) = s • L (1,0) + L (0,w)`. -/
theorem lcs_split_L (k : ℕ) (L : PP k →ₗ[ℝ] lcsM k) (s : ℝ) (w : lcsE k) :
    L ((s, w) : PP k) = s • L ((1 : ℝ), 0) + L ((0 : ℝ), w) := by
  rw [show ((s, w) : PP k) = s • ((1, 0) : PP k) + ((0, w) : PP k) from by
    ext <;> simp, map_add, map_smul]

/-- The sum of the `l`-th `v`-columns is `L` of the `v`-block. -/
theorem lcs_sum_smul_L (k : ℕ) (L : PP k →ₗ[ℝ] lcsM k) (v : lcsE k) :
    (∑ l : Fin k, v.ofLp l • L ((0 : ℝ), EuclideanSpace.single l 1)) = L ((0 : ℝ), v) := by
  have hsum : (LinearMap.prod (0 : lcsE k →ₗ[ℝ] ℝ) (LinearMap.id : lcsE k →ₗ[ℝ] lcsE k))
      (∑ l : Fin k, v.ofLp l • EuclideanSpace.single l 1)
      = ∑ l : Fin k, v.ofLp l • ((0 : ℝ), EuclideanSpace.single l 1) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun l _ => by rw [map_smul]; rfl)
  have h2 : ((0 : ℝ), v) = ∑ l : Fin k, v.ofLp l • ((0 : ℝ), EuclideanSpace.single l 1) := by
    rw [← hsum, lcs_sum_smul_single]
    simp [LinearMap.prod_apply]
  rw [h2, map_sum]
  exact Finset.sum_congr rfl (fun l _ => by rw [map_smul])

/-- **The composite `lcsSum F ∘ lcsLin` is `lensE`**: the frame's induced endomorphism, written
out on the model coordinates. -/
theorem lcsSum_lensF_eq (k : ℕ) (L : PP k →ₗ[ℝ] lcsM k) (c : ℝ) :
    (lcsSum (lensF k L c)).comp (lcsLin k) = lensE k L c := by
  apply LinearMap.ext
  intro ξ
  rw [LinearMap.comp_apply, lcsSum_apply]
  rw [show (∑ i, (lcsLin k ξ) i • lensF k L c i)
      = ∑ i, ((lcsT k) ξ).ofLp i • lensF k L c i from
    Finset.sum_congr rfl (fun i _ => by
      rw [show (lcsLin k ξ) i = ((lcsT k) ξ).ofLp i from by rw [lcsLin_apply, lcsT_apply]])]
  rw [lcsSum_cornerFrame, lensE_apply, lcs_sum_smul_L]
  simp only [smul_sub, smul_smul]
  rw [mul_comm ξ.2.1 c]
  module

/-! ## §4 The conjugate of `lensE` by the pairing `pairZ` -/

/-- The `(y,v)`-coordinates of `lensE`: `Yv ∘ lensE = -(c*y) • Yv ∘ L (1,0) + Yv ∘ L (0,v)`. -/
theorem lensE_Yv (k : ℕ) (L : PP k →ₗ[ℝ] lcsM k) (c : ℝ) (ξ : lcsM k) :
    Yv k (lensE k L c ξ) = (-(c * ξ.2.1)) • Yv k (L (1, 0)) + Yv k (L (0, ξ.2.2.2)) := by
  rw [lensE_apply]
  simp only [map_add, map_sub, map_smul, Yv_apply, Prod.mk_add_mk, Prod.mk_sub_mk, Prod.smul_mk,
    smul_eq_mul]
  ext <;> simp

/-- The `(x,u)`-coordinates of `lensE`. -/
theorem lensE_Xu (k : ℕ) (L : PP k →ₗ[ℝ] lcsM k) (c : ℝ) (ξ : lcsM k) :
    Xu k (lensE k L c ξ)
      = Xu k ξ + (c * ξ.2.1) • ((1, 0) : PP k) + Xu k (L (-c * ξ.2.1, ξ.2.2.2)) := by
  rw [lensE_apply, lcs_split_L k L (-c * ξ.2.1) ξ.2.2.2]
  simp only [map_add, map_sub, map_smul, Xu_apply, Prod.mk_add_mk, Prod.mk_sub_mk, Prod.smul_mk,
    smul_eq_mul]
  ext <;> simp <;> ring

/-- The `(y,v)`-part `A = (Yv ∘ L) ∘ T` of the conjugated endomorphism. -/
noncomputable def lensA (k : ℕ) (L : PP k →ₗ[ℝ] lcsM k) (c : ℝ) : PP k →ₗ[ℝ] PP k :=
  ((Yv k).comp L).comp (lensT k c)

/-- The `(x,u)`-part `B` of the conjugated endomorphism. -/
noncomputable def lensB (k : ℕ) (L : PP k →ₗ[ℝ] lcsM k) (c : ℝ) : PP k →ₗ[ℝ] PP k :=
  (((c : ℝ) • (LinearMap.fst ℝ ℝ (lcsE k))).prod (0 : PP k →ₗ[ℝ] lcsE k)) +
    ((Xu k).comp (L.comp (lensT k c)))

/-- The `(x,u)`-component of the conjugate of `lensE` by `pairZ`. -/
theorem lensE_conj_Xu (k : ℕ) (L : PP k →ₗ[ℝ] lcsM k) (c : ℝ) :
    (Xu k) ∘ₗ ((lensE k L c) ∘ₗ ↑((pairZ k).symm))
      = LinearMap.fst ℝ (PP k) (PP k) + (lensB k L c) ∘ₗ LinearMap.snd ℝ (PP k) (PP k) := by
  apply LinearMap.ext
  rintro ⟨⟨x, u⟩, ⟨y, v⟩⟩
  have hsymm : (pairZ k).symm ((x, u), (y, v)) = ((x, y, u, v) : lcsM k) := by
    apply (pairZ k).injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.add_apply]
  rw [hsymm, lensE_Xu]
  simp only [lensB, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.prod_apply, lensT_apply]
  ext <;> simp; ring

/-- The `(y,v)`-component of the conjugate of `lensE` by `pairZ`. -/
theorem lensE_conj_Yv (k : ℕ) (L : PP k →ₗ[ℝ] lcsM k) (c : ℝ) :
    (Yv k) ∘ₗ ((lensE k L c) ∘ₗ ↑((pairZ k).symm))
      = (lensA k L c) ∘ₗ LinearMap.snd ℝ (PP k) (PP k) := by
  apply LinearMap.ext
  rintro ⟨⟨x, u⟩, ⟨y, v⟩⟩
  have hsymm : (pairZ k).symm ((x, u), (y, v)) = ((x, y, u, v) : lcsM k) := by
    apply (pairZ k).injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.snd_apply]
  rw [hsymm, lensE_Yv]
  simp only [lensA, LinearMap.comp_apply, lensT_apply]
  rw [lcs_split_L k L (-c * y) v, map_add, map_smul]
  ring_nf

/-- **The conjugation of `lensE` by `pairZ` is block triangular**: the endomorphism
`(p,q) ↦ (p + B q, A q)` of `PP k × PP k`. -/
theorem lensE_conj (k : ℕ) (L : PP k →ₗ[ℝ] lcsM k) (c : ℝ) :
    (↑(pairZ k) : lcsM k →ₗ[ℝ] (PP k × PP k)) ∘ₗ ((lensE k L c) ∘ₗ ↑((pairZ k).symm))
      = ((LinearMap.id.comp (LinearMap.fst ℝ (PP k) (PP k))) +
          (lensB k L c).comp (LinearMap.snd ℝ (PP k) (PP k))).prod
        ((lensA k L c).comp (LinearMap.snd ℝ (PP k) (PP k))) := by
  rw [pairZ_eq_prod k, LinearMap.prod_comp, lensE_conj_Xu, lensE_conj_Yv]
  simp only [LinearMap.id_comp]

/-! ## §5 The bridge `lcsT = lcsLin` and the target -/

/-- The coordinate equivalence `lcsT` is `lcsLin` read in `WithLp`. -/
theorem lcsT_trans_eq_lcsLin (k : ℕ) :
    ((lcsT k).trans (WithLp.linearEquiv 2 ℝ (Fin (2 + k + k) → ℝ))).toLinearMap = lcsLin k := by
  apply LinearMap.ext
  intro ξ
  funext j
  simp [LinearEquiv.trans_apply, WithLp.linearEquiv, lcsLin, LinearMap.pi_apply]

/-- **The determinant of the corner frame of the framing chart** (the lead's `L1`): for
`L : PP k →ₗ Mdl k` the jet of the finger and a scalar `c`, the determinant of the frame
`[e_x, c • (e_x - L (1,0)), L (0,e_l), ιu_l]` read in the model coordinates is
`-c * det (Yv ∘ L)`. -/
theorem lensCornerDetOfChart {k : ℕ} (L : PP k →ₗ[ℝ] Work.Drive.Whitney.Mdl k) (c : ℝ) :
    frameDet (2 + k + k) (lcsT k)
      (Fin.append (Fin.append ![(1, 0, 0, 0),
          c • ((1, 0, 0, 0) - L ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))))]
        (fun l : Fin k => L ((0 : ℝ), EuclideanSpace.single l 1))) (iotaU k))
      = - c * LinearMap.det ((Yv k).comp L) := by
  rw [lcs_frameDet_eq, lcsT_trans_eq_lcsLin, lcsSum_lensF_eq]
  rw [← LinearMap.det_conj (lensE k L c) (pairZ k)]
  rw [lensE_conj, det_prod_block, LinearMap.det_id, one_mul]
  rw [lensA, LinearMap.det_comp, lensT_det]
  ring

end

end Work.Drive.PushDisc
