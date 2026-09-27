import Mathlib
import Submission.Work.Mostow.BdExt.bdMap
import Submission.Work.Mostow.BdExt.rayDist
import Submission.Work.Mostow.BdExt.closeSeq
import Submission.Work.Mostow.BdExt.isomConv
import Submission.Work.Mostow.BdExt.isomRayCompare
import Submission.Work.Mostow.BdExt.bdMapClose
import Submission.Work.Mostow.BdExt.rayBasic

/-!
# `bdMapEquiv`: the boundary extension is equivariant under coarse equivariance

`bdMap n Φ ξ` is the limit of the directions of the quasi-geodesic ray `Φ ∘ ray ξ`.  If `Φ` is a
quasi-isometry which is coarse-equivariant with respect to a pair of isometries `g, h`
(`hdist (Φ (g • u)) (h • Φ u) ≤ C₀` for all `u`), then the boundary extension is *exactly*
equivariant:

  `bdMap n Φ (bd g ξ) = bd h (bdMap n Φ ξ)`   for all `ξ ∈ Sph n`.

The argument is the classical one, carried out on sequences:

* `dirv (g • ray ξ k) → bd g ξ` (`isomConv`);
* the rays `g • ray ξ ·` and `ray (bd g ξ) ·` stay at bounded distance (`isomRayCompare`), hence so
  do their `Φ`-images, so `dirv (Φ (g • ray ξ k))` and `dirv (Φ (ray (bd g ξ) k))` have the same
  limit: by `closeSeq` and `bdMap_spec` the first converges to `bdMap n Φ (bd g ξ)`;
* the sequences `Φ (g • ray ξ k)` and `h • Φ (ray ξ k)` stay at bounded distance (by `heq`), so
  `dirv (h • Φ (ray ξ k)) → bdMap n Φ (bd g ξ)`;
* on the other hand `isomConv` applied to `h` along the escaping sequence `Φ (ray ξ k)` (whose
  directions converge to `bdMap n Φ ξ`) gives `dirv (h • Φ (ray ξ k)) → bd h (bdMap n Φ ξ)`.

Uniqueness of limits concludes.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow LeanEval.Geometry.MostowRigidity Filter

noncomputable section

variable {n : ℕ}

/-- The Euclidean norm of a sequence escapes to infinity as soon as its hyperbolic level does. -/
lemma tendsto_norm_of_tendsto_lvl {u : ℕ → E n}
    (h : Tendsto (fun k => lvl (u k)) atTop atTop) :
    Tendsto (fun k => ‖u k‖) atTop atTop := by
  have h1 : Tendsto (fun k => Real.sinh (lvl (u k))) atTop atTop :=
    tendsto_sinh_atTop'.comp h
  refine h1.congr' (Eventually.of_forall fun k => ?_)
  exact (norm_eq_sinh_lvl (u k)).symm

/-- The hyperbolic level is 1-Lipschitz: `lvl u - lvl v ≤ hdist u v`. -/
lemma lvl_sub_le_hdist (hI : HypIsometryProp n) (u v : E n) :
    lvl u - lvl v ≤ hdist u v := by
  obtain ⟨-, hsym, -, htri, -⟩ := hI
  simp only [lvl]
  have h := htri 0 v u
  rw [hsym u v]
  linarith

/-- A sequence at bounded distance from a sequence whose level escapes itself has escaping
level. -/
lemma tendsto_lvl_of_hdist_le (hI : HypIsometryProp n) {a b : ℕ → E n} {D : ℝ}
    (h : ∀ k, hdist (a k) (b k) ≤ D)
    (hb : Tendsto (fun k => lvl (b k)) atTop atTop) :
    Tendsto (fun k => lvl (a k)) atTop atTop := by
  have hshift : Tendsto (fun k => lvl (b k) + (-D)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-D) hb
  refine tendsto_atTop_mono (fun k => ?_) hshift
  have h1 := lvl_sub_le_hdist hI (b k) (a k)
  have h2 : hdist (b k) (a k) ≤ D := by
    rw [hI.2.1]; exact h k
  linarith

/-- The level of `g • u` is bounded below by the level of `u`, up to the level of `g • 0`. -/
lemma lvl_smul_ge (hI : HypIsometryProp n) (g : PO n 1) (u : E n) :
    lvl u - lvl (g • (0 : E n)) ≤ lvl (g • u) := by
  obtain ⟨-, hsym, -, htri, -, -, hiso, -⟩ := hI
  have h := htri (g • (0 : E n)) 0 (g • u)
  have his : hdist (g • (0 : E n)) (g • u) = hdist 0 u := hiso g 0 u
  have h0 : hdist (g • (0 : E n)) 0 = hdist 0 (g • (0 : E n)) := hsym _ _
  simp only [lvl] at h ⊢
  rw [his, h0] at h
  linarith

theorem bdMapEquiv (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Φ : Submission.Mostow.E n → Submission.Mostow.E n) (K C : ℝ) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hup : ∀ u v, Submission.Mostow.hdist (Φ u) (Φ v) ≤ K * Submission.Mostow.hdist u v + C)
    (hlow : ∀ u v, Submission.Mostow.hdist u v ≤ K * Submission.Mostow.hdist (Φ u) (Φ v) + C)
    (g h : LeanEval.Geometry.MostowRigidity.PO n 1) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (heq : ∀ u, Submission.Mostow.hdist (Φ (g • u)) (h • Φ u) ≤ C₀) :
    ∀ ξ ∈ Submission.Mostow.Sph n,
      Work.Mostow.BdExt.bdMap n Φ (Submission.Mostow.bd g ξ) =
        Submission.Mostow.bd h (Work.Mostow.BdExt.bdMap n Φ ξ) := by
  intro ξ hξ
  -- the boundary point `bd g ξ` lies on the sphere
  have hbdSph : ∀ (g : PO n 1) (ξ : E n), ξ ∈ Sph n → bd g ξ ∈ Sph n := by
    obtain ⟨-, -, -, -, -, -, -, h, -, -, -, -⟩ := hA
    exact h
  have hgξ : bd g ξ ∈ Sph n := hbdSph g ξ hξ
  -- the ray to `ξ` escapes to infinity, with directions tending to `ξ`
  have hlvl_u : Tendsto (fun k : ℕ => lvl (ray ξ (k : ℝ))) atTop atTop :=
    tendsto_lvl_ray ξ hξ
  have hdirv_u : Tendsto (fun k : ℕ => dirv (ray ξ (k : ℝ))) atTop (nhds ξ) :=
    tendsto_dirv_ray hI ξ hξ
  have hnorm_u : Tendsto (fun k : ℕ => ‖ray ξ (k : ℝ)‖) atTop atTop :=
    tendsto_norm_of_tendsto_lvl hlvl_u
  -- the image of the ray under `g` converges to `bd g ξ`
  have hgd : Tendsto (fun k : ℕ => dirv (g • ray ξ (k : ℝ))) atTop (nhds (bd g ξ)) :=
    isomConv n hA hI g (fun k : ℕ => ray ξ (k : ℝ)) ξ hξ hnorm_u hdirv_u
  -- the boundary map of `Φ` at `ξ` and at `bd g ξ`
  have hspecξ := bdMap_spec n hI Φ K C hK hC hup hlow ξ hξ
  have hspecgξ := bdMap_spec n hI Φ K C hK hC hup hlow (bd g ξ) hgξ
  -- the two rays are at bounded distance
  obtain ⟨D, hD, hDb⟩ := isomRayCompare n hA hI g ξ hξ
  -- the `Φ`-images of the two rays are at bounded distance
  have hclose12 : ∀ k : ℕ,
      hdist (Φ (g • ray ξ (k : ℝ))) (Φ (ray (bd g ξ) (k : ℝ))) ≤ K * D + C := by
    intro k
    have h1 := hup (g • ray ξ (k : ℝ)) (ray (bd g ξ) (k : ℝ))
    have h2 := hDb (k : ℝ) (Nat.cast_nonneg k)
    nlinarith [h1, h2, hK, hD]
  have hclose12' : ∀ k : ℕ,
      hdist (Φ (ray (bd g ξ) (k : ℝ))) (Φ (g • ray ξ (k : ℝ))) ≤ K * D + C :=
    fun k => by rw [hI.2.1]; exact hclose12 k
  have hD' : 0 ≤ K * D + C := by nlinarith [hK, hC, hD]
  -- the levels of the `Φ`-images escape
  have hlvl_2 : Tendsto (fun k : ℕ => lvl (Φ (ray (bd g ξ) (k : ℝ)))) atTop atTop :=
    tendsto_lvl_image_ray n hI Φ K C hK hC hlow (bd g ξ) hgξ
  have hlvl_1 : Tendsto (fun k : ℕ => lvl (Φ (g • ray ξ (k : ℝ)))) atTop atTop :=
    tendsto_lvl_of_hdist_le hI hclose12 hlvl_2
  -- hence the directions of the `Φ`-images of the first ray converge to `bdMap n Φ (bd g ξ)`
  have hseq1 : Tendsto (fun k : ℕ => dirv (Φ (g • ray ξ (k : ℝ)))) atTop
      (nhds (bdMap n Φ (bd g ξ))) :=
    closeSeq n hI (fun k : ℕ => Φ (ray (bd g ξ) (k : ℝ)))
      (fun k : ℕ => Φ (g • ray ξ (k : ℝ))) (K * D + C) hD' hclose12' hlvl_2 hlvl_1
      (bdMap n Φ (bd g ξ)) hspecgξ.2
  -- the level of `h • Φ (ray ξ ·)` also escapes
  have hlvl_a : Tendsto (fun k : ℕ => lvl (Φ (ray ξ (k : ℝ)))) atTop atTop :=
    tendsto_lvl_image_ray n hI Φ K C hK hC hlow ξ hξ
  have hlvl_3 : Tendsto (fun k : ℕ => lvl (h • Φ (ray ξ (k : ℝ)))) atTop atTop := by
    have hshift : Tendsto (fun k : ℕ => lvl (Φ (ray ξ (k : ℝ))) + (-(lvl (h • (0 : E n)))))
        atTop atTop :=
      tendsto_atTop_add_const_right atTop (-(lvl (h • (0 : E n)))) hlvl_a
    exact tendsto_atTop_mono (fun k => lvl_smul_ge hI h _) hshift
  -- `h • Φ (ray ξ ·)` is at bounded distance from the `Φ`-image of `g • ray ξ ·`
  have hclose13 : ∀ k : ℕ, hdist (Φ (g • ray ξ (k : ℝ))) (h • Φ (ray ξ (k : ℝ))) ≤ C₀ := by
    intro k
    calc hdist (Φ (g • ray ξ (k : ℝ))) (h • Φ (ray ξ (k : ℝ)))
        = hdist (h • Φ (ray ξ (k : ℝ))) (Φ (g • ray ξ (k : ℝ))) := (hI.2.1 _ _).symm
      _ ≤ C₀ := by
            rw [hI.2.1]
            exact heq (ray ξ (k : ℝ))
  have hseq3 : Tendsto (fun k : ℕ => dirv (h • Φ (ray ξ (k : ℝ)))) atTop
      (nhds (bdMap n Φ (bd g ξ))) :=
    closeSeq n hI (fun k : ℕ => Φ (g • ray ξ (k : ℝ)))
      (fun k : ℕ => h • Φ (ray ξ (k : ℝ))) C₀ hC₀ hclose13 hlvl_1 hlvl_3
      (bdMap n Φ (bd g ξ)) hseq1
  -- and finally `isomConv` identifies the same limit with `bd h (bdMap n Φ ξ)`
  have hnorm_a : Tendsto (fun k : ℕ => ‖Φ (ray ξ (k : ℝ))‖) atTop atTop :=
    tendsto_norm_of_tendsto_lvl hlvl_a
  have hseq3' : Tendsto (fun k : ℕ => dirv (h • Φ (ray ξ (k : ℝ)))) atTop
      (nhds (bd h (bdMap n Φ ξ))) :=
    isomConv n hA hI h (fun k : ℕ => Φ (ray ξ (k : ℝ))) (bdMap n Φ ξ) hspecξ.1 hnorm_a
      hspecξ.2
  exact tendsto_nhds_unique hseq3 hseq3'

end

end Work.Mostow.BdExt
