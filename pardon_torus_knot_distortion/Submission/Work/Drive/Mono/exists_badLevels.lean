import Mathlib
import Submission.Work.Drive.Mono.SlabCaps
import Submission.Work.Step2.closedBox_subset_closure_PBox
import Submission.Work.Topology.SphereSlicing.convex_PBox

namespace Work.Drive.Mono

set_option maxHeartbeats 400000

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal Topology RealInnerProductSpace

noncomputable section

/-! ## Point-set preliminaries for `exists_badLevels`

Throughout, `B := PBox s c σ` is Pardon's open box (open and convex, with
`closure B = {y | ∀ i, |y (σ i) - c (σ i)| ≤ boxSide i * s}` for `0 < s`), and `K := closure B`
is compact.  The two facts proved here are the ones the main argument needs:

* `combo_mem_PBox` — a point of the segment joining a point of the **open** box to a point of
  `K` (i.e. satisfying the closed-box coordinate bounds) lies in the open box, as long as the
  parameter is `< 1`.  This is what makes `sup` over `B ∩ H` and `max` over `K ∩ H` agree for a
  convex `H`.
* `seam_data` — for a convex closed `H` meeting the open box, the level functional `ℓ` has, on
  the compact set `K ∩ H`, an attained maximum `Q` with the property that a level `lam` at which
  `K ∩ H` meets `{ℓ = lam}` but `B ∩ H` has no point above `lam` must equal `Q`. -/

/-- The **vertices** of the box `PBox s c σ`: the points whose every coordinate is at an extreme
of the box. -/
private def boxVertex (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) (ε : Fin 3 → Bool) : R3 :=
  WithLp.toLp 2 (fun j : Fin 3 => c j + (if ε (σ.symm j) then (1:ℝ) else -1) *
    Submission.boxSide (σ.symm j) * s)

/-- The **midpoint of a box edge parallel to the direction `σ i`**: the `σ i`-coordinate is the
centre coordinate, the two others are at extremes. -/
private def boxEdgeMid (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) (i : Fin 3)
    (ε : Fin 3 → Bool) : R3 :=
  WithLp.toLp 2 (fun k : Fin 3 => c k + (if k = σ i then (0:ℝ) else
    (if ε (σ.symm k) then (1:ℝ) else -1) * Submission.boxSide (σ.symm k) * s))

private lemma boxVertex_apply (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) (ε : Fin 3 → Bool)
    (i : Fin 3) :
    boxVertex c σ s ε (σ i) = c (σ i) + (if ε i then (1:ℝ) else -1) *
      Submission.boxSide i * s := by
  simp [boxVertex]

private lemma boxEdgeMid_apply (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) (i : Fin 3)
    (ε : Fin 3 → Bool) : boxEdgeMid c σ s i ε (σ i) = c (σ i) := by
  simp [boxEdgeMid]

private lemma boxEdgeMid_apply_ne (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) (i j : Fin 3)
    (ε : Fin 3 → Bool) (h : j ≠ i) :
    boxEdgeMid c σ s i ε (σ j) = c (σ j) + (if ε j then (1:ℝ) else -1) *
      Submission.boxSide j * s := by
  have hne : σ j ≠ σ i := fun hh => h (σ.injective hh)
  simp [boxEdgeMid, hne]

private lemma abs_sign (b : Bool) : |(if b then (1:ℝ) else -1)| = 1 := by
  by_cases h : b <;> simp [h]

private lemma abs_signed_mul (b : Bool) (A : ℝ) (hA : 0 < A) :
    |(if b then (1:ℝ) else -1) * A| = A := by
  rw [abs_mul, abs_sign, one_mul, abs_of_pos hA]

private lemma boxNorm_le_of_coord_le {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {y : R3}
    (h : ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s) :
    Submission.boxNorm c σ y ≤ s := by
  rw [Submission.boxNorm, max_le_iff, max_le_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [div_le_iff₀ (Submission.boxSide_pos 0)]; simpa [mul_comm] using h 0
  · rw [div_le_iff₀ (Submission.boxSide_pos 1)]; simpa [mul_comm] using h 1
  · rw [div_le_iff₀ (Submission.boxSide_pos 2)]; simpa [mul_comm] using h 2

/-- A point satisfying the closed-box coordinate bounds lies in the closure of the open box. -/
private lemma mem_closure_PBox_of_coord_le {s : ℝ} (hs : 0 < s) {c : R3}
    {σ : Equiv.Perm (Fin 3)} {y : R3}
    (h : ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s) :
    y ∈ closure (Submission.PBox s c σ) :=
  Work.Step2.closedBox_subset_closure_PBox hs c σ (boxNorm_le_of_coord_le h)

/-- Every point of the closure of the box satisfies the closed-box coordinate bounds. -/
private lemma closure_PBox_coord_le {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {y : R3}
    (hy : y ∈ closure (Submission.PBox s c σ)) (i : Fin 3) :
    |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s := by
  have hsub : Submission.PBox s c σ ⊆
      {z : R3 | ∀ i : Fin 3, |z (σ i) - c (σ i)| ≤ Submission.boxSide i * s} :=
    fun z hz i => le_of_lt (hz i)
  have hcl : IsClosed {z : R3 | ∀ i : Fin 3,
      |z (σ i) - c (σ i)| ≤ Submission.boxSide i * s} := by
    have : {z : R3 | ∀ i : Fin 3, |z (σ i) - c (σ i)| ≤ Submission.boxSide i * s}
        = ⋂ i : Fin 3, {z : R3 | |z (σ i) - c (σ i)| ≤ Submission.boxSide i * s} := by
      ext z; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
  exact closure_minimal hsub hcl hy i

private lemma boxVertex_mem_closure {s : ℝ} (hs : 0 < s) {c : R3} {σ : Equiv.Perm (Fin 3)}
    (ε : Fin 3 → Bool) : boxVertex c σ s ε ∈ closure (Submission.PBox s c σ) := by
  refine mem_closure_PBox_of_coord_le hs (fun i => ?_)
  rw [boxVertex_apply, show c (σ i) + (if ε i then (1:ℝ) else -1) *
        Submission.boxSide i * s - c (σ i)
      = (if ε i then (1:ℝ) else -1) * (Submission.boxSide i * s) by ring,
    abs_signed_mul _ _ (mul_pos (Submission.boxSide_pos i) hs)]

private lemma boxEdgeMid_mem_closure {s : ℝ} (hs : 0 < s) {c : R3} {σ : Equiv.Perm (Fin 3)}
    (i : Fin 3) (ε : Fin 3 → Bool) :
    boxEdgeMid c σ s i ε ∈ closure (Submission.PBox s c σ) := by
  refine mem_closure_PBox_of_coord_le hs (fun j => ?_)
  by_cases hji : j = i
  · subst hji
    rw [boxEdgeMid_apply, sub_self, abs_zero]
    exact le_of_lt (mul_pos (Submission.boxSide_pos j) hs)
  · rw [boxEdgeMid_apply_ne c σ s i j ε hji,
      show c (σ j) + (if ε j then (1:ℝ) else -1) * Submission.boxSide j * s - c (σ j)
        = (if ε j then (1:ℝ) else -1) * (Submission.boxSide j * s) by ring,
      abs_signed_mul _ _ (mul_pos (Submission.boxSide_pos j) hs)]

/-- A convex combination, with coefficient `< 1`, of a point of the open box and a point of its
closure lies in the open box. -/
private lemma combo_mem_PBox {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {x y : R3}
    (hx : x ∈ Submission.PBox s c σ)
    (hy : ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (1 - t) • x + t • y ∈ Submission.PBox s c σ := by
  rw [Submission.mem_PBox]
  intro i
  have hz : ((1 - t) • x + t • y) (σ i) - c (σ i)
      = (1 - t) * (x (σ i) - c (σ i)) + t * (y (σ i) - c (σ i)) := by
    simp only [PiLp.add_apply, PiLp.smul_apply]
    ring
  rw [hz]
  have h1 : (1 - t) * |x (σ i) - c (σ i)| < (1 - t) * (Submission.boxSide i * s) :=
    mul_lt_mul_of_pos_left (hx i) (by linarith)
  have h2 : t * |y (σ i) - c (σ i)| ≤ t * (Submission.boxSide i * s) :=
    mul_le_mul_of_nonneg_left (hy i) ht0
  calc |(1 - t) * (x (σ i) - c (σ i)) + t * (y (σ i) - c (σ i))|
      ≤ (1 - t) * |x (σ i) - c (σ i)| + t * |y (σ i) - c (σ i)| := by
        have h := abs_add_le ((1 - t) * (x (σ i) - c (σ i))) (t * (y (σ i) - c (σ i)))
        rwa [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t),
          abs_of_nonneg ht0] at h
    _ < (1 - t) * (Submission.boxSide i * s) + t * (Submission.boxSide i * s) := by linarith
    _ = Submission.boxSide i * s := by ring

private lemma isCompact_closure_PBox {s : ℝ} (hs : 0 < s) (c : R3)
    (σ : Equiv.Perm (Fin 3)) : IsCompact (closure (Submission.PBox s c σ)) := by
  refine Bornology.IsBounded.isCompact_closure ?_
  exact Bornology.IsBounded.subset (Metric.isBounded_ball (x := c) (r := (5 / 2) * s))
    (Submission.PBox_subset_ball s (le_of_lt hs) c σ)

/-! ### Convexity and closedness of the three seams -/

private lemma convex_inner_eq (v : R3) (A : ℝ) : Convex ℝ {y : R3 | inner ℝ v y = A} := by
  intro x hx y hy a b ha hb hab
  show inner ℝ v (a • x + b • y) = A
  have hx' : inner ℝ v x = A := hx
  have hy' : inner ℝ v y = A := hy
  rw [inner_add_right, inner_smul_right, inner_smul_right, hx', hy', ← add_mul, hab, one_mul]

private lemma convex_inner_le (v : R3) (A : ℝ) : Convex ℝ {y : R3 | inner ℝ v y ≤ A} := by
  intro x hx y hy a b ha hb hab
  show inner ℝ v (a • x + b • y) ≤ A
  have hx' : inner ℝ v x ≤ A := hx
  have hy' : inner ℝ v y ≤ A := hy
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  have h : a * A + b * A = A := by rw [← add_mul, hab, one_mul]
  linarith [mul_le_mul_of_nonneg_left hx' ha, mul_le_mul_of_nonneg_left hy' hb]

private lemma convex_le_inner (v : R3) (A : ℝ) : Convex ℝ {y : R3 | A ≤ inner ℝ v y} := by
  intro x hx y hy a b ha hb hab
  show A ≤ inner ℝ v (a • x + b • y)
  have hx' : A ≤ inner ℝ v x := hx
  have hy' : A ≤ inner ℝ v y := hy
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  have h : a * A + b * A = A := by rw [← add_mul, hab, one_mul]
  linarith [mul_le_mul_of_nonneg_left hx' ha, mul_le_mul_of_nonneg_left hy' hb]

private lemma abs_inner_le_iff (A h : ℝ) (x : ℝ) :
    |x - A| ≤ h ↔ A - h ≤ x ∧ x ≤ A + h := by
  rw [abs_le]
  constructor <;> intro hh <;> exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

private lemma set_eq_abs_inner_le (v : R3) (A h : ℝ) :
    {y : R3 | |inner ℝ v y - A| ≤ h}
      = {y : R3 | A - h ≤ inner ℝ v y} ∩ {y : R3 | inner ℝ v y ≤ A + h} := by
  ext y
  simp only [Set.mem_inter_iff]
  exact abs_inner_le_iff A h (inner ℝ v y)

private lemma convex_abs_inner_le (v : R3) (A h : ℝ) :
    Convex ℝ {y : R3 | |inner ℝ v y - A| ≤ h} := by
  rw [set_eq_abs_inner_le]
  exact (convex_le_inner v (A - h)).inter (convex_inner_le v (A + h))

private lemma isClosed_inner_eq (v : R3) (A : ℝ) : IsClosed {y : R3 | inner ℝ v y = A} :=
  isClosed_eq (continuous_const.inner continuous_id) continuous_const

private lemma isClosed_abs_inner_le (v : R3) (A h : ℝ) :
    IsClosed {y : R3 | |inner ℝ v y - A| ≤ h} := by
  rw [set_eq_abs_inner_le]
  exact (isClosed_le continuous_const (continuous_const.inner continuous_id)).inter
    (isClosed_le (continuous_const.inner continuous_id) continuous_const)

/-! ### Points of the open box on a prescribed level of `⟪v,·⟫` -/

/-- If the open box contains a point strictly below and a point strictly above the level `A` of
`⟪v,·⟫`, then it contains a point on that level (convexity plus the intermediate value property of
the affine function `⟪v,·⟫` along a segment). -/
private lemma exists_mem_PBox_inner_eq {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3}
    {A : ℝ} {yp ym : R3} (hyp : yp ∈ Submission.PBox s c σ) (hym : ym ∈ Submission.PBox s c σ)
    (hlt : inner ℝ v ym < A) (hgt : A < inner ℝ v yp) :
    ∃ z ∈ Submission.PBox s c σ, inner ℝ v z = A := by
  set t : ℝ := (inner ℝ v yp - A) / (inner ℝ v yp - inner ℝ v ym) with htdef
  have hden : 0 < inner ℝ v yp - inner ℝ v ym := by linarith
  have hnum : 0 < inner ℝ v yp - A := by linarith
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  have ht1 : t < 1 := by rw [htdef, div_lt_one hden]; linarith
  refine ⟨(1 - t) • yp + t • ym, ?_, ?_⟩
  · exact (Work.Topology.SphereSlicing.convex_PBox s c σ) hyp hym (by linarith) ht0 (by ring)
  · rw [inner_add_right, inner_smul_right, inner_smul_right, htdef]
    field_simp
    ring

/-- **The closed slab really cuts the box across its width**: `SlabCutsBox` with `0 < h` forces
the upper face `{⟪v,·⟫ = ⟪v,c⟫+u+h}` to meet the *open* box. -/
private lemma exists_mem_PBox_facePlus {s u h : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    (hh : 0 < h) (hcut : SlabCutsBox s c σ (inner ℝ v c + u) h v) :
    (Submission.PBox s c σ ∩ {y : R3 | inner ℝ v y = inner ℝ v c + u + h}).Nonempty := by
  obtain ⟨⟨yp, hyp, hgtp⟩, ⟨ym, hym, hltm⟩⟩ := hcut
  obtain ⟨z, hzP, hz⟩ := exists_mem_PBox_inner_eq hyp hym (by linarith) hgtp
  exact ⟨z, hzP, hz⟩

private lemma exists_mem_PBox_faceMinus {s u h : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    (hh : 0 < h) (hcut : SlabCutsBox s c σ (inner ℝ v c + u) h v) :
    (Submission.PBox s c σ ∩ {y : R3 | inner ℝ v y = inner ℝ v c + u - h}).Nonempty := by
  obtain ⟨⟨yp, hyp, hgtp⟩, ⟨ym, hym, hltm⟩⟩ := hcut
  obtain ⟨z, hzP, hz⟩ := exists_mem_PBox_inner_eq hyp hym hltm (by linarith)
  exact ⟨z, hzP, hz⟩

private lemma exists_mem_PBox_slab {s u h : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    (hh : 0 < h) (hcut : SlabCutsBox s c σ (inner ℝ v c + u) h v) :
    (Submission.PBox s c σ ∩ {y : R3 | |inner ℝ v y - (inner ℝ v c + u)| ≤ h}).Nonempty := by
  obtain ⟨z, hzP, hz⟩ := exists_mem_PBox_facePlus hh hcut
  refine ⟨z, hzP, ?_⟩
  have hz' : inner ℝ v z = inner ℝ v c + u + h := hz
  show |inner ℝ v z - (inner ℝ v c + u)| ≤ h
  rw [hz']
  have habs : |h| = h := abs_of_nonneg (le_of_lt hh)
  rw [show inner ℝ v c + u + h - (inner ℝ v c + u) = h by ring, habs]

/-! ### The seam values -/

/-- **The seam value of a convex closed set `H` meeting the open box.**

`ℓ` attains a maximum `Q` on the compact set `K ∩ H` (`K = closure (PBox s c σ)`), and a level
`lam` at which `K ∩ H` meets the wall `{ℓ = lam}` while `B ∩ H` has no point strictly above `lam`
must equal that maximum.  The geometric content is that `sup` of `ℓ` over `B ∩ H` equals the `max`
over `K ∩ H`: membership of the segment points `(1-t) z + t y` in the open box for `t < 1`
(`combo_mem_PBox`) gives both inequalities as `t → 1`. -/
private lemma seam_data {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ}
    {lam0 lam1 : ℝ} {H : Set R3}
    (hwin : ∀ y ∈ closure (Submission.PBox s c σ), lam0 < ℓ y ∧ ℓ y < lam1)
    (hKcomp : IsCompact (closure (Submission.PBox s c σ)))
    (hHconv : Convex ℝ H) (hHcl : IsClosed H)
    (hPKH : (Submission.PBox s c σ ∩ H).Nonempty) :
    ∃ Q : ℝ, (lam0 < Q ∧ Q < lam1) ∧
      ((closure (Submission.PBox s c σ) ∩ H).Nonempty →
        (∃ ym ∈ closure (Submission.PBox s c σ) ∩ H, ℓ ym = Q ∧
          ∀ y ∈ closure (Submission.PBox s c σ) ∩ H, ℓ y ≤ Q) ∧
        (∀ lam : ℝ, (∃ y ∈ closure (Submission.PBox s c σ) ∩ H, ℓ y = lam) →
          (∀ z ∈ Submission.PBox s c σ ∩ H, ℓ z ≤ lam) → lam = Q)) := by
  classical
  have hlam : lam0 < lam1 := by
    obtain ⟨z, hz⟩ := hPKH
    have h1 := hwin z (subset_closure hz.1)
    linarith [h1.1, h1.2]
  by_cases hY : (closure (Submission.PBox s c σ) ∩ H).Nonempty
  · obtain ⟨w, hwKH, hwmax⟩ :=
      (hKcomp.inter_right hHcl).exists_isMaxOn hY ℓ.continuous.continuousOn
    refine ⟨ℓ w, ⟨(hwin w hwKH.1).1, (hwin w hwKH.1).2⟩, fun _ => ⟨⟨w, hwKH, rfl, ?_⟩, ?_⟩⟩
    · intro y hy; exact hwmax hy
    · intro lam hprem hbound
      have h1 : lam ≤ ℓ w := by
        obtain ⟨y, hyKH, hylam⟩ := hprem
        rw [← hylam]; exact hwmax hyKH
      have h2 : ℓ w ≤ lam := by
        by_contra hcon
        push Not at hcon
        obtain ⟨z0, hz0P, hz0H⟩ := hPKH
        set g : ℝ → ℝ := fun t => ℓ ((1 - t) • z0 + t • w) with hgdef
        have hgcont : Continuous g := by
          have h1 : Continuous fun t : ℝ => (1 - t) • z0 + t • w := by fun_prop
          exact ℓ.continuous.comp h1
        have hε : 0 < ℓ w - lam := by linarith
        obtain ⟨δ, hδpos, hδ⟩ :=
          Metric.continuousAt_iff.mp hgcont.continuousAt (ℓ w - lam) hε
        set t : ℝ := 1 - min δ 1 / 2 with htdef
        have hδ1 : (0:ℝ) < min δ 1 := lt_min hδpos one_pos
        have ht_lt1 : t < 1 := by rw [htdef]; linarith [div_pos hδ1 two_pos]
        have ht_ge0 : 0 ≤ t := by
          rw [htdef]
          have : min δ 1 / 2 ≤ 1 / 2 := by have h := min_le_right δ 1; linarith
          linarith
        have hdist : dist t 1 < δ := by
          rw [Real.dist_eq, htdef]
          have h1 : |1 - min δ 1 / 2 - 1| = min δ 1 / 2 := by
            rw [show (1 : ℝ) - min δ 1 / 2 - 1 = -(min δ 1 / 2) by ring, abs_neg,
              abs_of_nonneg (by positivity)]
          rw [h1]
          have h2 : min δ 1 / 2 < δ := by have := min_le_left δ 1; linarith
          linarith
        have hclose := hδ hdist
        have hmem : ((1 - t) • z0 + t • w) ∈ Submission.PBox s c σ ∩ H :=
          ⟨combo_mem_PBox hz0P (fun i => closure_PBox_coord_le hwKH.1 i) ht_ge0 ht_lt1,
           hHconv hz0H hwKH.2 (by linarith) (by linarith) (by ring)⟩
        have hle := hbound _ hmem
        have hgt : lam < g t := by
          have h2 := hclose
          rw [Real.dist_eq] at h2
          have hg1 : g 1 = ℓ w := by simp [hgdef]
          rw [hg1] at h2
          have := abs_lt.mp h2
          linarith [this.1]
        have hgt' : g t = ℓ ((1 - t) • z0 + t • w) := rfl
        rw [hgt'] at hgt
        linarith
      exact le_antisymm h1 h2
  · exact ⟨(lam0 + lam1) / 2, ⟨by linarith, by linarith⟩, fun hY' => absurd hY' hY⟩

end

open LeanEval.KnotTheory.PardonDistortion Set in
open scoped ENNReal Topology in
/-- **The degenerate levels of the tilted-sweep frontier are finite.**

For the tilt data of the sweep (`ℓ v = 0`, `ℓ ≠ 0`, a slab of positive half-width `0 < h` whose
two faces really separate the box in the sense of `SlabCutsBox`, and a window `(lam0, lam1)`
containing the `ℓ`-range of the **closed** box), there is a finite set `B` of levels, contained in
the window, such that at every level `lam ∈ Icc lam0 lam1` outside `exc ∪ B`:

* the wall `{ℓ = lam}` is nowhere parallel to a box edge at whose (extremal) point it passes
  (`hedge` of `Work.Drive.Mono.tiltedLevel_disjoint_spheres`);
* the wall does not pass through a vertex of the box (`hvertex`);
* each of the three slab faces inside the closed box meets the open box strictly above `lam`, as
  soon as it meets the closed box at `lam` (`hseam`).

The set `B` is the union of the finitely many `ℓ`-values of the box vertices, of the box edge points
at which the wall is parallel to the edge, and of the three extremal `ℓ`-values `Q₊`, `Q₋`, `β` of
the three slab faces inside the closed box (the levels at which the seam of the frontier pinches).
All of them are `ℓ`-values of points of `closure (PBox)`, so they lie in the window by the closed-box
window hypothesis; the key step is that the *supremum* over the open box of `ℓ` on a plane (or on
the closed slab) meeting the box equals the *maximum* over the closed box (take the segment from a
point of the open intersection to a point attaining the maximum: its relative interior lies in the
open box, because the box is open and convex; here `0 < h` guarantees that the three faces
`⟪v,·⟫ = ⟪v,c⟫ + u ± h` and `|⟪v,·⟫ - (⟪v,c⟫+u)| ≤ h` all meet the *open* box, which
`SlabCutsBox` alone does not: with `h < 0` the "upper" face can lie outside the box and the
conclusion fails). -/
theorem exists_badLevels {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    {exc : Finset ℝ} {lam0 lam1 s u : ℝ}
    (hh : 0 < h) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hcut : Work.Drive.Mono.SlabCutsBox s c σ (inner ℝ v c + u) h v)
    (hwin : ∀ y ∈ closure (Submission.PBox s c σ), lam0 < ℓ y ∧ ℓ y < lam1) :
    ∃ B : Finset ℝ, (∀ t ∈ B, lam0 < t ∧ t < lam1) ∧
      ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ ((exc ∪ B : Finset ℝ) : Set ℝ) →
        (∀ (i : Fin 3) (ε : Fin 3 → Bool),
          lam = ℓ (WithLp.toLp 2 (fun k : Fin 3 => c k +
            (if k = σ i then (0 : ℝ) else
              (if ε (σ.symm k) then 1 else -1) * Submission.boxSide (σ.symm k) * s))) →
          ℓ (EuclideanSpace.single (σ i) (1 : ℝ)) ≠ 0) ∧
        (∀ ε : Fin 3 → Bool,
          lam ≠ ℓ (WithLp.toLp 2 (fun j : Fin 3 => c j +
            (if ε (σ.symm j) then 1 else -1) * Submission.boxSide (σ.symm j) * s))) ∧
        ((∃ y ∈ closure (Submission.PBox s c σ),
            inner ℝ v y = inner ℝ v c + u + h ∧ ℓ y = lam) →
          (∃ z ∈ Submission.PBox s c σ,
            inner ℝ v z = inner ℝ v c + u + h ∧ lam < ℓ z)) ∧
        ((∃ y ∈ closure (Submission.PBox s c σ),
            inner ℝ v y = inner ℝ v c + u - h ∧ ℓ y = lam) →
          (∃ z ∈ Submission.PBox s c σ,
            inner ℝ v z = inner ℝ v c + u - h ∧ lam < ℓ z)) ∧
        ((∃ y ∈ closure (Submission.PBox s c σ),
            |inner ℝ v y - (inner ℝ v c + u)| ≤ h ∧ ℓ y = lam) →
          (∃ z ∈ Submission.PBox s c σ,
            |inner ℝ v z - (inner ℝ v c + u)| ≤ h ∧ lam < ℓ z)) := by
  classical
  have hcut' := hcut
  obtain ⟨⟨yp, hyp, hgtp⟩, ⟨ym, hym, hltm⟩⟩ := hcut'
  -- the box has positive size
  have hs : 0 < s := by
    have h0 := hyp 0
    rw [Submission.boxSide_zero, one_mul] at h0
    linarith [abs_nonneg (yp (σ 0) - c (σ 0))]
  have hKcomp : IsCompact (closure (Submission.PBox s c σ)) :=
    isCompact_closure_PBox hs c σ
  -- the three seam values
  obtain ⟨QP, hQPwin, hQPspec⟩ :=
    seam_data (H := {y : R3 | inner ℝ v y = inner ℝ v c + u + h}) hwin hKcomp
      (convex_inner_eq v _) (isClosed_inner_eq v _) (exists_mem_PBox_facePlus hh hcut)
  obtain ⟨QM, hQMwin, hQMspec⟩ :=
    seam_data (H := {y : R3 | inner ℝ v y = inner ℝ v c + u - h}) hwin hKcomp
      (convex_inner_eq v _) (isClosed_inner_eq v _) (exists_mem_PBox_faceMinus hh hcut)
  obtain ⟨β, hβwin, hβspec⟩ :=
    seam_data (H := {y : R3 | |inner ℝ v y - (inner ℝ v c + u)| ≤ h}) hwin hKcomp
      (convex_abs_inner_le v _ _) (isClosed_abs_inner_le v _ _) (exists_mem_PBox_slab hh hcut)
  -- the exceptional set
  let V : Finset ℝ := Finset.univ.image (fun ε : Fin 3 → Bool => ℓ (boxVertex c σ s ε))
  let E : Finset ℝ := Finset.univ.image
    (fun p : Fin 3 × (Fin 3 → Bool) => ℓ (boxEdgeMid c σ s p.1 p.2))
  let B : Finset ℝ := (V ∪ E) ∪ ({QP, QM, β} : Finset ℝ)
  have hVmem : ∀ ε : Fin 3 → Bool, ℓ (boxVertex c σ s ε) ∈ V := by
    intro ε
    show ℓ (boxVertex c σ s ε) ∈ Finset.univ.image
      (fun ε' : Fin 3 → Bool => ℓ (boxVertex c σ s ε'))
    exact Finset.mem_image.mpr ⟨ε, Finset.mem_univ ε, rfl⟩
  have hEmem : ∀ (i : Fin 3) (ε : Fin 3 → Bool), ℓ (boxEdgeMid c σ s i ε) ∈ E := by
    intro i ε
    show ℓ (boxEdgeMid c σ s i ε) ∈ Finset.univ.image
      (fun p : Fin 3 × (Fin 3 → Bool) => ℓ (boxEdgeMid c σ s p.1 p.2))
    exact Finset.mem_image.mpr ⟨(i, ε), Finset.mem_univ _, rfl⟩
  have hBVE : ∀ t : ℝ, t ∈ V ∪ E → t ∈ B := by
    intro t ht
    show t ∈ (V ∪ E) ∪ ({QP, QM, β} : Finset ℝ)
    exact Finset.mem_union_left ({QP, QM, β} : Finset ℝ) ht
  have hBQP : QP ∈ B := by
    show QP ∈ (V ∪ E) ∪ ({QP, QM, β} : Finset ℝ)
    exact Finset.mem_union_right (V ∪ E) (Finset.mem_insert_self QP _)
  have hBQM : QM ∈ B := by
    show QM ∈ (V ∪ E) ∪ ({QP, QM, β} : Finset ℝ)
    exact Finset.mem_union_right (V ∪ E)
      (Finset.mem_insert_of_mem (Finset.mem_insert_self QM _))
  have hBβ : β ∈ B := by
    show β ∈ (V ∪ E) ∪ ({QP, QM, β} : Finset ℝ)
    exact Finset.mem_union_right (V ∪ E)
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self β)))
  have hBwin : ∀ t ∈ B, lam0 < t ∧ t < lam1 := by
    intro t ht
    rcases Finset.mem_union.mp (show t ∈ (V ∪ E) ∪ ({QP, QM, β} : Finset ℝ) from ht) with ht | ht
    · rcases Finset.mem_union.mp (show t ∈ V ∪ E from ht) with ht | ht
      · obtain ⟨ε, -, rfl⟩ := Finset.mem_image.mp (show t ∈ Finset.univ.image
            (fun ε' : Fin 3 → Bool => ℓ (boxVertex c σ s ε')) from ht)
        exact hwin _ (boxVertex_mem_closure hs ε)
      · obtain ⟨pp, -, rfl⟩ := Finset.mem_image.mp (show t ∈ Finset.univ.image
            (fun p : Fin 3 × (Fin 3 → Bool) => ℓ (boxEdgeMid c σ s p.1 p.2)) from ht)
        exact hwin _ (boxEdgeMid_mem_closure hs pp.1 pp.2)
    · rcases Finset.mem_insert.mp (show t ∈ insert QP (insert QM (insert β ∅)) from ht) with
        rfl | ht
      · exact hQPwin
      · rcases Finset.mem_insert.mp (show t ∈ insert QM (insert β ∅) from ht) with rfl | ht
        · exact hQMwin
        · have htβ : t ∈ ({β} : Finset ℝ) := ht
          rw [Finset.mem_singleton] at htβ
          rw [htβ]
          exact hβwin
  refine ⟨B, hBwin, ?_⟩
  intro lam hlamI hnotB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the wall is not parallel to an edge it meets
    intro i ε heq
    exfalso
    apply hnotB
    rw [Finset.mem_coe]
    have hE : lam ∈ E := by rw [heq]; exact hEmem i ε
    exact Finset.mem_union_right exc (hBVE lam (Finset.mem_union_right V hE))
  · -- the wall misses the vertices
    intro ε heq
    exfalso
    apply hnotB
    rw [Finset.mem_coe]
    have hV : lam ∈ V := by rw [heq]; exact hVmem ε
    exact Finset.mem_union_right exc (hBVE lam (Finset.mem_union_left E hV))
  · -- the upper face of the slab
    rintro ⟨y, hyK, hyH, hylam⟩
    by_contra hcon
    push Not at hcon
    have hY : (closure (Submission.PBox s c σ) ∩
        {y : R3 | inner ℝ v y = inner ℝ v c + u + h}).Nonempty := ⟨y, hyK, hyH⟩
    obtain ⟨⟨ym, _, _, hymmax⟩, hpart2⟩ := hQPspec hY
    have h1 : lam ≤ QP := by
      rw [← hylam]
      exact hymmax y ⟨hyK, hyH⟩
    have h2 : QP ≤ lam :=
      le_of_eq (hpart2 lam ⟨y, ⟨hyK, hyH⟩, hylam⟩ (fun z hz => hcon z hz.1 hz.2)).symm
    have h3 : lam = QP := le_antisymm h1 h2
    exact hnotB (Finset.mem_coe.mpr (Finset.mem_union_right exc (h3 ▸ hBQP)))
  · -- the lower face of the slab
    rintro ⟨y, hyK, hyH, hylam⟩
    by_contra hcon
    push Not at hcon
    have hY : (closure (Submission.PBox s c σ) ∩
        {y : R3 | inner ℝ v y = inner ℝ v c + u - h}).Nonempty := ⟨y, hyK, hyH⟩
    obtain ⟨⟨ym, _, _, hymmax⟩, hpart2⟩ := hQMspec hY
    have h1 : lam ≤ QM := by
      rw [← hylam]
      exact hymmax y ⟨hyK, hyH⟩
    have h2 : QM ≤ lam :=
      le_of_eq (hpart2 lam ⟨y, ⟨hyK, hyH⟩, hylam⟩ (fun z hz => hcon z hz.1 hz.2)).symm
    have h3 : lam = QM := le_antisymm h1 h2
    exact hnotB (Finset.mem_coe.mpr (Finset.mem_union_right exc (h3 ▸ hBQM)))
  · -- the closed slab
    rintro ⟨y, hyK, hyH, hylam⟩
    by_contra hcon
    push Not at hcon
    have hY : (closure (Submission.PBox s c σ) ∩
        {y : R3 | |inner ℝ v y - (inner ℝ v c + u)| ≤ h}).Nonempty := ⟨y, hyK, hyH⟩
    obtain ⟨⟨ym, _, _, hymmax⟩, hpart2⟩ := hβspec hY
    have h1 : lam ≤ β := by
      rw [← hylam]
      exact hymmax y ⟨hyK, hyH⟩
    have h2 : β ≤ lam :=
      le_of_eq (hpart2 lam ⟨y, ⟨hyK, hyH⟩, hylam⟩ (fun z hz => hcon z hz.1 hz.2)).symm
    have h3 : lam = β := le_antisymm h1 h2
    exact hnotB (Finset.mem_coe.mpr (Finset.mem_union_right exc (h3 ▸ hBβ)))

end Work.Drive.Mono
