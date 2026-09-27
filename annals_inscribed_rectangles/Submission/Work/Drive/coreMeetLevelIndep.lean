import Mathlib
import Submission.Work.Drive.sideCountDefs
import Submission.Work.Drive.clampedSweepLevel
import Submission.Work.Drive.clampedSweepChart

/-!
# The level independence of the box meet count, **without faithfulness**

`Work.Drive.coreMeet Q c P` is the box meet set of the planar core loop of a chart `Q` against the
*radially clamped* sweep of a plane presentation `P` at the truncation level `c`
(`Submission/Work/Drive/sideCountDefs.lean`), and `Work.Drive.coreSideCount Q c P` is its cardinality.

`Work.Drive.odd_coreSideCount_eq_of_lt_level` (`Submission/Work/Drive/germLevelBridge.lean`) proves the
level independence of the *parity* of this count, but only through the **geometric** (point) count, i.e.
under the hypothesis `hinj` that the loop parameter determines the meet — the *faithfulness* of the box
parameterisation, which is **not** a genericity consequence of `GoodPair` and can fail
(`Submission/Work/Drive/GEOMETRIC_LOCALITY_STATUS.md` §9).  The germ lane's cross-level parity
obligation (`hparA`/`hparN` of `Work.Drive.sideGerm_add_neg_eq_one_of_refTripleEngine`) is therefore not
reachable through that statement.

This file proves the sharper fact: the **count itself** (not only its parity) is independent of the
truncation level, for the radial cutoff `ψ = 1 - ·`, when

* the level of the loop is above both truncation levels (`hloop`, `hloop'`),
* the level of every plane point of the box is above both truncation levels (`hr`, `hr'`),
* and the meets are *interior in the radial parameter* (`hint`, `hint'`) — which is exactly the
  interiority clause of `GoodPair`.

The proof is a bijection between the two meet sets: the sweep's radial parameter is the **unique**
solution of the level equation `levelOf (clampedSweep c ψ P (y, t)) = L`
(`Work.Drive.existsUnique_levelOf_clampedSweep_eq`), so replacing the truncation level `c` by `c'`
leaves the plane parameters `(y 0, y 1)` of a meet unchanged and moves the radial parameter by a
bijection.  No faithfulness hypothesis occurs.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff

set_option maxHeartbeats 800000

noncomputable section


open Manifold Set
open scoped Manifold ContDiff

set_option maxHeartbeats 800000


private lemma radVec_mk2_eta (x : EuclideanSpace ℝ (Fin 3)) :
    radVec (mk2 (x 0) (x 1)) (x 2) = x := by
  ext i
  fin_cases i <;> simp [radVec]

private lemma mk2_radVec (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    mk2 ((radVec y t) 0) ((radVec y t) 1) = y := by
  rw [radVec_apply_zero, radVec_apply_one]
  exact mk2_eta y

private lemma mk2_radVec_ofLp (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    mk2 ((radVec y t).ofLp 0) ((radVec y t).ofLp 1) = y := by
  rw [show (radVec y t).ofLp 0 = (radVec y t) 0 from rfl,
    show (radVec y t).ofLp 1 = (radVec y t) 1 from rfl]
  exact mk2_radVec y t

private lemma levelOf_clampedSweep_radVec (c : ℝ) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    levelOf (clampedSweep c (fun s => 1 - s) P (radVec y t))
      = Real.exp ((1 - t) * (Real.log c - Real.log (levelOf (P y)))) * levelOf (P y) := by
  rw [levelOf_clampedSweep]
  have h : clampScale c (fun s => 1 - s) P (radVec y t)
      = Real.exp ((1 - t) * (Real.log c - Real.log (levelOf (P y)))) := by
    rw [clampScale, radVec_apply_two, mk2_radVec_ofLp]
  rw [h, mk2_radVec_ofLp]

private lemma unitBox1_of_unitBox2 {p : EuclideanSpace ℝ (Fin 3)}
    (hp : p ∈ Submission.Drive.unitBox 2) :
    mk2 (p 0) (p 1) ∈ Submission.Drive.unitBox 1 := by
  intro i
  fin_cases i
  · simpa [mk2_apply_zero] using hp 0
  · simpa [mk2_apply_one] using hp 1

private lemma radVec_mem_unitBox {y : EuclideanSpace ℝ (Fin 2)} {t : ℝ}
    (hy : y ∈ Submission.Drive.unitBox 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    radVec y t ∈ Submission.Drive.unitBox 2 := by
  intro i
  fin_cases i
  · simpa [radVec] using hy 0
  · simpa [radVec] using hy 1
  · simpa [radVec] using ht

/-- The unique radial parameter realizing a level. -/
private noncomputable def levelParam (c : ℝ) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (y : EuclideanSpace ℝ (Fin 2)) (L : ℝ) : ℝ := by
  classical
  exact if h : ∃! t : ℝ, t ∈ Set.Ioo (0:ℝ) 1 ∧
      levelOf (clampedSweep c (fun s => 1 - s) P (radVec y t)) = L then h.choose else 0

private lemma levelParam_spec {c : ℝ} {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {y : EuclideanSpace ℝ (Fin 2)} {L : ℝ}
    (h : ∃! t : ℝ, t ∈ Set.Ioo (0:ℝ) 1 ∧
      levelOf (clampedSweep c (fun s => 1 - s) P (radVec y t)) = L) :
    levelParam c P y L ∈ Set.Ioo (0:ℝ) 1 ∧
      levelOf (clampedSweep c (fun s => 1 - s) P (radVec y (levelParam c P y L))) = L := by
  rw [levelParam, dif_pos h]
  exact h.choose_spec.1

private lemma levelParam_eq {c : ℝ} {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {y : EuclideanSpace ℝ (Fin 2)} {L : ℝ}
    (h : ∃! t : ℝ, t ∈ Set.Ioo (0:ℝ) 1 ∧
      levelOf (clampedSweep c (fun s => 1 - s) P (radVec y t)) = L)
    {s : ℝ}
    (hs : s ∈ Set.Ioo (0:ℝ) 1 ∧
      levelOf (clampedSweep c (fun s => 1 - s) P (radVec y s)) = L) :
    levelParam c P y L = s := by
  rw [levelParam, dif_pos h]
  exact (h.choose_spec.2 s hs).symm

section Main

variable {Q : ℂ → CappingSpace} {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}

/-- The map moving a box meet at one level to the corresponding meet at another level. -/
private noncomputable def levelShiftMap (c' : ℝ) (Q : ℂ → CappingSpace)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (p : ℝ × Amb 2) : ℝ × Amb 2 :=
  (p.1, radVec (mk2 (p.2 0) (p.2 1))
    (levelParam c' P (mk2 (p.2 0) (p.2 1)) (levelOf (coreLoop Q p.1))))

private lemma psi0 : (fun s : ℝ => 1 - s) 0 = 1 := by norm_num
private lemma psi1 : (fun s : ℝ => 1 - s) 1 = 0 := by norm_num
private lemma psicont : ContinuousOn (fun s : ℝ => 1 - s) (Set.Icc (0:ℝ) 1) :=
  (continuous_const.sub continuous_id).continuousOn
private lemma psianti : StrictAntiOn (fun s : ℝ => 1 - s) (Set.Icc (0:ℝ) 1) := by
  intro a ha b hb hab; dsimp only; linarith

/-- The level of the loop at a meet is strictly below the level of the plane point. -/
private lemma loopLevel_lt_planeLevel_of_mem_coreMeet {c : ℝ} (hc : 0 < c)
    (hloop : ∀ t ∈ Set.Icc (0:ℝ) 1, c < levelOf (coreLoop Q t))
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (hint : ∀ p ∈ coreMeet Q c P, p.2 2 ∈ Set.Ioo (0:ℝ) 1)
    {p : ℝ × Amb 2} (hp : p ∈ coreMeet Q c P) :
    levelOf (coreLoop Q p.1) < levelOf (P (mk2 (p.2 0) (p.2 1))) := by
  have hint2 : p.2 2 ∈ Set.Ioo (0:ℝ) 1 := hint p hp
  obtain ⟨h1, h2, h3⟩ := hp
  have hy : mk2 (p.2 0) (p.2 1) ∈ Submission.Drive.unitBox 1 := unitBox1_of_unitBox2 h2
  have hℓc : c ≤ levelOf (P (mk2 (p.2 0) (p.2 1))) := hr _ hy
  have hL : levelOf (coreLoop Q p.1) = levelOf (clampedSweep c (fun s => 1 - s) P p.2) := by
    rw [h3]
  have hp2 : p.2 = radVec (mk2 (p.2 0) (p.2 1)) (p.2 2) := (radVec_mk2_eta p.2).symm
  have hℓne : c ≠ levelOf (P (mk2 (p.2 0) (p.2 1))) := by
    intro heq
    have : levelOf (coreLoop Q p.1) = c := by
      rw [hL, hp2, levelOf_clampedSweep_radVec, heq, sub_self, mul_zero, Real.exp_zero,
        one_mul]
    linarith [hloop p.1 h1]
  have hlog : Real.log c - Real.log (levelOf (P (mk2 (p.2 0) (p.2 1)))) < 0 := by
    have h2' : Real.log c < Real.log (levelOf (P (mk2 (p.2 0) (p.2 1)))) :=
      Real.log_lt_log hc (lt_of_le_of_ne hℓc hℓne)
    linarith
  have hℓpos : 0 < levelOf (P (mk2 (p.2 0) (p.2 1))) := levelOf_pos _
  have hexp : Real.exp ((1 - p.2 2) * (Real.log c - Real.log (levelOf (P (mk2 (p.2 0) (p.2 1)))))) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (by linarith [hint2.2]) hlog
  rw [hL, hp2, levelOf_clampedSweep_radVec]
  calc Real.exp ((1 - p.2 2) *
        (Real.log c - Real.log (levelOf (P (mk2 (p.2 0) (p.2 1))))))
        * levelOf (P (mk2 (p.2 0) (p.2 1)))
      < 1 * levelOf (P (mk2 (p.2 0) (p.2 1))) :=
        mul_lt_mul_of_pos_right hexp hℓpos
    _ = levelOf (P (mk2 (p.2 0) (p.2 1))) := one_mul _


/-- The unique radial parameter at a prescribed level. -/
private lemma hexists_sweep (c : ℝ) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (hc : 0 < c)
    {y : EuclideanSpace ℝ (Fin 2)} {L : ℝ} (h1 : c < L) (h2 : L < levelOf (P y)) :
    ∃! t : ℝ, t ∈ Set.Ioo (0:ℝ) 1 ∧
      levelOf (clampedSweep c (fun s => 1 - s) P (radVec y t)) = L :=
  existsUnique_levelOf_clampedSweep_eq (c := c) (P := P) (y := y) (L := L) hc
    psi0 psi1 psicont psianti h1 h2
/-- **The image of the level-shift map is a meet at the new level.** -/
private lemma levelShiftMap_mem {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c')
    (hloop : ∀ t ∈ Set.Icc (0:ℝ) 1, c < levelOf (coreLoop Q t))
    (hloop' : ∀ t ∈ Set.Icc (0:ℝ) 1, c' < levelOf (coreLoop Q t))
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (hint : ∀ p ∈ coreMeet Q c P, p.2 2 ∈ Set.Ioo (0:ℝ) 1)
    {p : ℝ × Amb 2} (hp : p ∈ coreMeet Q c P) :
    levelShiftMap c' Q P p ∈ coreMeet Q c' P := by
  obtain ⟨t, y⟩ := p
  have h1 : t ∈ Set.Icc (0:ℝ) 1 := hp.1
  have h2 : y ∈ Submission.Drive.unitBox 2 := hp.2.1
  have h3 : coreLoop Q t = clampedSweep c (fun s => 1 - s) P y := hp.2.2
  have hy : mk2 (y 0) (y 1) ∈ Submission.Drive.unitBox 1 := unitBox1_of_unitBox2 h2
  have hLlt : levelOf (coreLoop Q t) < levelOf (P (mk2 (y 0) (y 1))) :=
    loopLevel_lt_planeLevel_of_mem_coreMeet hc hloop hr hint hp
  have hLc' : c' < levelOf (coreLoop Q t) := hloop' t h1
  obtain ⟨hy2, hspec⟩ := levelParam_spec (hexists_sweep c' P hc' hLc' hLlt)
  have hpoint : coreLoop Q t = clampedSweep c' (fun s => 1 - s) P
      (radVec (mk2 (y 0) (y 1))
        (levelParam c' P (mk2 (y 0) (y 1)) (levelOf (coreLoop Q t)))) := by
    refine cappingSpaceHomeoProj.injective (Prod.ext ?_ ?_)
    · exact Subtype.ext (by simpa only [levelOf] using hspec.symm)
    · calc (cappingSpaceHomeoProj (coreLoop Q t)).2
          = (cappingSpaceHomeoProj (clampedSweep c (fun s => 1 - s) P y)).2 := by rw [h3]
        _ = (cappingSpaceHomeoProj (P (mk2 (y 0) (y 1)))).2 := cls_clampedSweep c _ P y
        _ = (cappingSpaceHomeoProj (clampedSweep c' (fun s => 1 - s) P
              (radVec (mk2 (y 0) (y 1))
                (levelParam c' P (mk2 (y 0) (y 1)) (levelOf (coreLoop Q t)))))).2 := by
            rw [cls_clampedSweep, mk2_radVec_ofLp]
  exact ⟨h1, radVec_mem_unitBox hy ⟨le_of_lt hy2.1, le_of_lt hy2.2⟩, hpoint⟩

/-- **The level-shift map is injective on the meet set.** -/
private lemma levelShiftMap_inj {c c' : ℝ} (hc : 0 < c)
    (hloop : ∀ t ∈ Set.Icc (0:ℝ) 1, c < levelOf (coreLoop Q t))
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (hint : ∀ p ∈ coreMeet Q c P, p.2 2 ∈ Set.Ioo (0:ℝ) 1)
    {p p' : ℝ × Amb 2} (hp : p ∈ coreMeet Q c P) (hp' : p' ∈ coreMeet Q c P)
    (heq : levelShiftMap c' Q P p = levelShiftMap c' Q P p') : p = p' := by
  obtain ⟨t, y⟩ := p
  obtain ⟨s', z⟩ := p'
  have h1 : t ∈ Set.Icc (0:ℝ) 1 := hp.1
  have h2 : y ∈ Submission.Drive.unitBox 2 := hp.2.1
  have h3 : coreLoop Q t = clampedSweep c (fun s => 1 - s) P y := hp.2.2
  have h2' : z ∈ Submission.Drive.unitBox 2 := hp'.2.1
  have h3' : coreLoop Q s' = clampedSweep c (fun s => 1 - s) P z := hp'.2.2
  have hy3 : y = radVec (mk2 (y 0) (y 1)) (y 2) := (radVec_mk2_eta y).symm
  have hy3' : z = radVec (mk2 (z 0) (z 1)) (z 2) := (radVec_mk2_eta z).symm
  have ht : t = s' := by
    simpa [levelShiftMap] using congrArg Prod.fst heq
  have hvec : radVec (mk2 (y 0) (y 1))
        (levelParam c' P (mk2 (y 0) (y 1)) (levelOf (coreLoop Q t)))
      = radVec (mk2 (z 0) (z 1))
        (levelParam c' P (mk2 (z 0) (z 1)) (levelOf (coreLoop Q s'))) := by
    simpa [levelShiftMap] using congrArg Prod.snd heq
  have h01 : mk2 (y 0) (y 1) = mk2 (z 0) (z 1) := by
    have h0 : radVec (mk2 (y 0) (y 1))
          (levelParam c' P (mk2 (y 0) (y 1)) (levelOf (coreLoop Q t))) 0
        = radVec (mk2 (z 0) (z 1))
          (levelParam c' P (mk2 (z 0) (z 1)) (levelOf (coreLoop Q s'))) 0 := by
      rw [hvec]
    have h1'' : radVec (mk2 (y 0) (y 1))
          (levelParam c' P (mk2 (y 0) (y 1)) (levelOf (coreLoop Q t))) 1
        = radVec (mk2 (z 0) (z 1))
          (levelParam c' P (mk2 (z 0) (z 1)) (levelOf (coreLoop Q s'))) 1 := by
      rw [hvec]
    simp only [radVec] at h0 h1''
    ext i
    fin_cases i
    · simpa [mk2_apply_zero] using h0
    · simpa [mk2_apply_one] using h1''
  have hLlt : levelOf (coreLoop Q t) < levelOf (P (mk2 (y 0) (y 1))) :=
    loopLevel_lt_planeLevel_of_mem_coreMeet hc hloop hr hint hp
  have hLc : c < levelOf (coreLoop Q t) := hloop t h1
  have hy2 : y 2 = levelParam c P (mk2 (y 0) (y 1)) (levelOf (coreLoop Q t)) :=
    (levelParam_eq (hexists_sweep c P hc hLc hLlt) ⟨hint (t, y) hp, by rw [h3, ← hy3]⟩).symm
  have hlev' : levelOf (clampedSweep c (fun s => 1 - s) P (radVec (mk2 (y 0) (y 1)) (z 2)))
      = levelOf (coreLoop Q t) := by
    have e1 : radVec (mk2 (y 0) (y 1)) (z 2) = z := by
      rw [h01]
      exact radVec_mk2_eta z
    have e2 : levelOf (clampedSweep c (fun s => 1 - s) P (radVec (mk2 (y 0) (y 1)) (z 2)))
        = levelOf (clampedSweep c (fun s => 1 - s) P z) :=
      congrArg (fun x => levelOf (clampedSweep c (fun s => 1 - s) P x)) e1
    rw [e2, ← h3', ht]
  have hy2' : z 2 = levelParam c P (mk2 (y 0) (y 1)) (levelOf (coreLoop Q t)) :=
    (levelParam_eq (hexists_sweep c P hc hLc hLlt) ⟨hint (s', z) hp', hlev'⟩).symm
  have hlast : y 2 = z 2 := by rw [hy2, hy2']
  exact Prod.ext ht (hy3.trans ((by rw [h01, hlast] : radVec (mk2 (y 0) (y 1)) (y 2)
      = radVec (mk2 (z 0) (z 1)) (z 2)).trans hy3'.symm))

/-- **Surjectivity of the level-shift map.** -/
private lemma levelShiftMap_surj {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c')
    (hloop : ∀ t ∈ Set.Icc (0:ℝ) 1, c < levelOf (coreLoop Q t))
    (hloop' : ∀ t ∈ Set.Icc (0:ℝ) 1, c' < levelOf (coreLoop Q t))
    (hr' : ∀ y ∈ Submission.Drive.unitBox 1, c' ≤ levelOf (P y))
    (hint' : ∀ p ∈ coreMeet Q c' P, p.2 2 ∈ Set.Ioo (0:ℝ) 1)
    {b : ℝ × Amb 2} (hb : b ∈ coreMeet Q c' P) :
    ∃ a ∈ coreMeet Q c P, levelShiftMap c' Q P a = b := by
  obtain ⟨t, y⟩ := b
  have h1 : t ∈ Set.Icc (0:ℝ) 1 := hb.1
  have h2 : y ∈ Submission.Drive.unitBox 2 := hb.2.1
  have h3 : coreLoop Q t = clampedSweep c' (fun s => 1 - s) P y := hb.2.2
  have hy : mk2 (y 0) (y 1) ∈ Submission.Drive.unitBox 1 := unitBox1_of_unitBox2 h2
  have hy3 : y = radVec (mk2 (y 0) (y 1)) (y 2) := (radVec_mk2_eta y).symm
  have hLlt : levelOf (coreLoop Q t) < levelOf (P (mk2 (y 0) (y 1))) :=
    loopLevel_lt_planeLevel_of_mem_coreMeet hc' hloop' hr' hint' hb
  have hLc : c < levelOf (coreLoop Q t) := hloop t h1
  obtain ⟨hy2mem, hspec⟩ := levelParam_spec (hexists_sweep c P hc hLc hLlt)
  have hpoint : coreLoop Q t = clampedSweep c (fun s => 1 - s) P
      (radVec (mk2 (y 0) (y 1)) (levelParam c P (mk2 (y 0) (y 1)) (levelOf (coreLoop Q t)))) := by
    refine cappingSpaceHomeoProj.injective (Prod.ext ?_ ?_)
    · exact Subtype.ext (by simpa only [levelOf] using hspec.symm)
    · calc (cappingSpaceHomeoProj (coreLoop Q t)).2
          = (cappingSpaceHomeoProj (clampedSweep c' (fun s => 1 - s) P y)).2 := by rw [h3]
        _ = (cappingSpaceHomeoProj (P (mk2 (y 0) (y 1)))).2 := cls_clampedSweep c' _ P y
        _ = (cappingSpaceHomeoProj (clampedSweep c (fun s => 1 - s) P
              (radVec (mk2 (y 0) (y 1)) (levelParam c P (mk2 (y 0) (y 1)) (levelOf (coreLoop Q t)))))).2 := by
            rw [cls_clampedSweep, mk2_radVec_ofLp]
  refine ⟨(t, radVec (mk2 (y 0) (y 1)) (levelParam c P (mk2 (y 0) (y 1)) (levelOf (coreLoop Q t)))), ?_, ?_⟩
  · exact ⟨h1, radVec_mem_unitBox hy ⟨le_of_lt hy2mem.1, le_of_lt hy2mem.2⟩, hpoint⟩
  · have hval : levelParam c' P (mk2 (y 0) (y 1)) (levelOf (coreLoop Q t)) = y 2 :=
      levelParam_eq (hexists_sweep c' P hc' (hloop' t h1) hLlt)
        ⟨hint' (t, y) hb, by rw [h3, ← hy3]⟩
    have hval2 : radVec (mk2 (y 0) (y 1))
        (levelParam c' P (mk2 (y 0) (y 1)) (levelOf (coreLoop Q t))) = y := by
      rw [hval, ← hy3]
    show levelShiftMap c' Q P
      (t, radVec (mk2 (y 0) (y 1)) (levelParam c P (mk2 (y 0) (y 1)) (levelOf (coreLoop Q t))))
        = (t, y)
    simp only [levelShiftMap, mk2_radVec_ofLp]
    exact Prod.ext rfl hval2

/-- **The level independence of the box count of a meet set, as an *equality* of cardinalities**,
   for the radial cutoff `ψ = 1 - ·`, given that the meets are interior. -/
theorem coreMeet_ncard_eq_of_lt_level {c c' : ℝ}
    (hc : 0 < c) (hc' : 0 < c')
    (hloop : ∀ t ∈ Set.Icc (0:ℝ) 1, c < levelOf (coreLoop Q t))
    (hloop' : ∀ t ∈ Set.Icc (0:ℝ) 1, c' < levelOf (coreLoop Q t))
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (hr' : ∀ y ∈ Submission.Drive.unitBox 1, c' ≤ levelOf (P y))
    (hint : ∀ p ∈ coreMeet Q c P, p.2 2 ∈ Set.Ioo (0:ℝ) 1)
    (hint' : ∀ p ∈ coreMeet Q c' P, p.2 2 ∈ Set.Ioo (0:ℝ) 1) :
    (coreMeet Q c P).ncard = (coreMeet Q c' P).ncard :=
  Set.ncard_congr (fun p _ => levelShiftMap c' Q P p)
    (fun p hp => levelShiftMap_mem hc hc' hloop hloop' hr hint hp)
    (fun p p' hp hp' heq => levelShiftMap_inj hc hloop hr hint hp hp' heq)
    (fun b hb => by
      obtain ⟨a, ha, heq⟩ := levelShiftMap_surj hc hc' hloop hloop' hr' hint' hb
      exact ⟨a, ha, heq⟩)

end Main

end

end Work.Drive
