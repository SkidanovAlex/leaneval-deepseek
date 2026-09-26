import Mathlib
import Submission.Work.Core.Torus

/-!
# The extrinsic systole of a parametrised torus

Let `psi : ℝ → ℝ → ℝ³` be a continuous parametrisation of an embedded torus: it is
`2π`-periodic in each variable and injective modulo `2π`.  The main result of this
file, `Work.Geometry.diameter_systole`, states that there is a positive constant
`ρ`, depending only on `psi`, such that the image of *every* essential closed curve
on the torus (a curve whose lift to the parameter plane winds by a nonzero vector
`(a,b)`) has diameter at least `ρ`.

The mathematical content is the following *uniform local injectivity* statement,
proved in `exists_uniform_sheet_radius`: there is `ρ > 0` such that whenever two
parameter points `p, z` have `psi`-images at distance `< ρ`, the point `z` lies in
the "sheet" `ball (p, π) + 2πℤ²`.  Equivalently: the preimage of any ball of
radius `ρ` in the image is a disjoint union of sheets on each of which `psi` is
injective.  The constant `π` is the injectivity radius of the parameter torus
`ℝ²/2πℤ²`: two distinct points with the same image differ by a period vector of
norm at least `2π`.

The proof of `exists_uniform_sheet_radius` is elementary: if the statement failed,
one would obtain parameter points `pₙ, zₙ` with `psi`-images closer and closer and
with `zₙ` at distance `≥ π` from every lattice translate of `pₙ`; reducing modulo
the period lattice and passing to a convergent subsequence (the fundamental domain
`[0,2π]²` is compact) contradicts the continuity of `psi` together with the
discreteness of the lattice.

This is the "extrinsic systole" input used in Pardon's proof of the torus-knot
distortion bound.
-/

open Set Filter
open scoped Topology

namespace Work.Geometry

noncomputable section

/-- The period lattice `2πℤ² ⊂ ℝ × ℝ` of the parameter plane. -/
def lat : AddSubgroup (ℝ × ℝ) where
  carrier := {p : ℝ × ℝ | ∃ k l : ℤ, p = ((k : ℝ) * (2 * Real.pi), (l : ℝ) * (2 * Real.pi))}
  zero_mem' := ⟨0, 0, by ext <;> simp⟩
  add_mem' := by
    rintro p q ⟨k, l, rfl⟩ ⟨k', l', rfl⟩
    refine ⟨k + k', l + l', ?_⟩
    ext <;> simp <;> ring
  neg_mem' := by
    rintro p ⟨k, l, rfl⟩
    refine ⟨-k, -l, ?_⟩
    ext <;> simp

/-- The fundamental domain `[0, 2π]²` of the period lattice. -/
def Fund : Set (ℝ × ℝ) := Set.Icc (0:ℝ) (2 * Real.pi) ×ˢ Set.Icc (0:ℝ) (2 * Real.pi)

/-- The parametrisation as a single map on the parameter plane `ℝ × ℝ`. -/
def pMap (psi : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) : ℝ × ℝ → EuclideanSpace ℝ (Fin 3) :=
  fun p => psi p.1 p.2

@[simp] lemma pMap_apply (psi : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (p : ℝ × ℝ) :
    pMap psi p = psi p.1 p.2 := rfl

/-- A nonzero element of the period lattice has norm at least `2π` (in the product
metric on `ℝ × ℝ`). -/
lemma lat_norm_ge {p : ℝ × ℝ} (hp : p ∈ lat) (h0 : p ≠ 0) : 2 * Real.pi ≤ ‖p‖ := by
  obtain ⟨k, l, rfl⟩ := hp
  have hpos : (0:ℝ) < 2 * Real.pi := by positivity
  rw [Prod.norm_def]
  have hk : ‖((k:ℝ) * (2*Real.pi))‖ = |(k:ℝ)| * (2*Real.pi) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
  have hl : ‖((l:ℝ) * (2*Real.pi))‖ = |(l:ℝ)| * (2*Real.pi) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
  rw [hk, hl]
  have hne : (k, l) ≠ 0 := by
    intro h
    apply h0
    have h1 : k = 0 := by simpa using congrArg Prod.fst h
    have h2 : l = 0 := by simpa using congrArg Prod.snd h
    simp [h1, h2]
  have hmax : (1:ℝ) ≤ max |(k:ℝ)| |(l:ℝ)| := by
    rcases eq_or_ne k 0 with hk0 | hk0
    · have hl0 : l ≠ 0 := by rintro rfl; exact hne (by simp [hk0])
      have : (1:ℤ) ≤ |l| := by have : (0:ℤ) < |l| := abs_pos.mpr hl0; omega
      have : (1:ℝ) ≤ |(l:ℝ)| := by exact_mod_cast this
      exact le_trans this (le_max_right _ _)
    · have : (1:ℤ) ≤ |k| := by have : (0:ℤ) < |k| := abs_pos.mpr hk0; omega
      have : (1:ℝ) ≤ |(k:ℝ)| := by exact_mod_cast this
      exact le_trans this (le_max_left _ _)
  have hmaxmul : max (|(k:ℝ)| * (2*Real.pi)) (|(l:ℝ)| * (2*Real.pi))
      = max |(k:ℝ)| |(l:ℝ)| * (2*Real.pi) := by rw [max_mul_of_nonneg _ _ (le_of_lt hpos)]
  rw [hmaxmul]
  nlinarith [hmax, hpos]

/-- Any parameter point can be translated by a period vector into the fundamental
domain `[0,2π]²`. -/
lemma exists_lat_sub_mem_Fund (z : ℝ × ℝ) : ∃ m ∈ lat, z - m ∈ Fund := by
  have hpos : (0:ℝ) < 2 * Real.pi := by positivity
  have key : ∀ x : ℝ, 0 ≤ x - ⌊x / (2*Real.pi)⌋ * (2*Real.pi) ∧
      x - ⌊x / (2*Real.pi)⌋ * (2*Real.pi) < 2 * Real.pi := by
    intro x
    have h : x - ⌊x / (2*Real.pi)⌋ * (2*Real.pi)
          = Int.fract (x / (2*Real.pi)) * (2*Real.pi) := by
      rw [Int.fract]; field_simp
    rw [h]
    exact ⟨mul_nonneg (Int.fract_nonneg _) (le_of_lt hpos),
      by simpa using mul_lt_mul_of_pos_right (Int.fract_lt_one _) hpos⟩
  refine ⟨(⌊z.1 / (2*Real.pi)⌋ * (2*Real.pi), ⌊z.2 / (2*Real.pi)⌋ * (2*Real.pi)), ?_, ?_⟩
  · exact ⟨⌊z.1 / (2*Real.pi)⌋, ⌊z.2 / (2*Real.pi)⌋, rfl⟩
  · rw [Fund, Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
    simp only [Prod.fst_sub, Prod.snd_sub]
    exact ⟨⟨(key z.1).1, (key z.1).2.le⟩, ⟨(key z.2).1, (key z.2).2.le⟩⟩

/-- The same, in one real variable: translating by an integer multiple of `2π`
lands in `[0, 2π]`. -/
lemma exists_int_sub_mem_Icc (t : ℝ) :
    ∃ k : ℤ, t - (k:ℝ) * (2 * Real.pi) ∈ Set.Icc (0:ℝ) (2 * Real.pi) := by
  have hpos : (0:ℝ) < 2 * Real.pi := by positivity
  refine ⟨⌊t / (2*Real.pi)⌋, ?_⟩
  have h : t - (⌊t / (2*Real.pi)⌋:ℝ) * (2*Real.pi)
        = Int.fract (t / (2*Real.pi)) * (2*Real.pi) := by
    rw [Int.fract]; field_simp
  rw [Set.mem_Icc, h]
  exact ⟨mul_nonneg (Int.fract_nonneg _) (le_of_lt hpos),
    by simpa using (mul_lt_mul_of_pos_right (Int.fract_lt_one _) hpos).le⟩

/-- The parametrisation is invariant under the period lattice. -/
lemma pMap_add_lat (psi : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hper1 : ∀ x y, psi (x + 2 * Real.pi) y = psi x y)
    (hper2 : ∀ x y, psi x (y + 2 * Real.pi) = psi x y)
    {p m : ℝ × ℝ} (hm : m ∈ lat) : pMap psi (p + m) = pMap psi p := by
  obtain ⟨k, l, rfl⟩ := hm
  have h1 : Function.Periodic (fun x => psi x (p.2 + (l:ℝ) * (2*Real.pi))) (2*Real.pi) :=
    fun x => hper1 x (p.2 + (l:ℝ) * (2*Real.pi))
  have h2 : Function.Periodic (fun y => psi p.1 y) (2*Real.pi) := fun y => hper2 p.1 y
  show psi (p.1 + (k:ℝ) * (2*Real.pi)) (p.2 + (l:ℝ) * (2*Real.pi)) = psi p.1 p.2
  calc psi (p.1 + (k:ℝ) * (2*Real.pi)) (p.2 + (l:ℝ) * (2*Real.pi))
      = psi p.1 (p.2 + (l:ℝ) * (2*Real.pi)) := (h1.int_mul k) p.1
    _ = psi p.1 p.2 := (h2.int_mul l) p.2

/-- Two parameter points have the same image under `psi` exactly when they differ
by a period-lattice element. -/
lemma pMap_eq_iff (psi : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hinj : ∀ x y x' y', psi x y = psi x' y' ↔
      (∃ k : ℤ, x = x' + k * (2 * Real.pi)) ∧ (∃ k : ℤ, y = y' + k * (2 * Real.pi)))
    (p q : ℝ × ℝ) : pMap psi p = pMap psi q ↔ p - q ∈ lat := by
  show psi p.1 p.2 = psi q.1 q.2 ↔ p - q ∈ lat
  rw [hinj]
  constructor
  · rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
    refine ⟨k, l, ?_⟩
    ext
    · show p.1 - q.1 = (k:ℝ) * (2*Real.pi); linarith
    · show p.2 - q.2 = (l:ℝ) * (2*Real.pi); linarith
  · rintro ⟨k, l, h⟩
    have h1 : p.1 - q.1 = (k:ℝ) * (2*Real.pi) := by simpa using congrArg Prod.fst h
    have h2 : p.2 - q.2 = (l:ℝ) * (2*Real.pi) := by simpa using congrArg Prod.snd h
    exact ⟨⟨k, by linarith⟩, ⟨l, by linarith⟩⟩

/-- **Uniform local injectivity of a parametrised torus.**  There is `ρ > 0` such
that any two parameter points whose images are closer than `ρ` lie in the same
sheet of the period-lattice covering: the second is within `π` of a lattice
translate of the first. -/
lemma exists_uniform_sheet_radius (psi : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hper1 : ∀ x y, psi (x + 2 * Real.pi) y = psi x y)
    (hper2 : ∀ x y, psi x (y + 2 * Real.pi) = psi x y)
    (hinj : ∀ x y x' y', psi x y = psi x' y' ↔
      (∃ k : ℤ, x = x' + k * (2 * Real.pi)) ∧ (∃ k : ℤ, y = y' + k * (2 * Real.pi)))
    (hcont : Continuous (fun p : ℝ × ℝ => psi p.1 p.2)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ p z : ℝ × ℝ,
      dist (pMap psi p) (pMap psi z) < ρ → ∃ m ∈ lat, dist z (p + m) < Real.pi := by
  have hcont' : Continuous (pMap psi) := hcont
  by_contra hcon
  push Not at hcon
  choose pp zz hpz using fun n : ℕ => hcon (1/((n:ℝ)+1)) (by positivity)
  choose T hTl hTF using fun n : ℕ => exists_lat_sub_mem_Fund (pp n)
  choose U hUl hUF using fun n : ℕ => exists_lat_sub_mem_Fund (zz n - T n)
  let q : ℕ → ℝ × ℝ := fun n => pp n - T n
  let r : ℕ → ℝ × ℝ := fun n => zz n - T n - U n
  let W : ℕ → ℝ × ℝ := fun n => T n + U n
  have hqF : ∀ n, q n ∈ Fund := fun n => hTF n
  have hrF : ∀ n, r n ∈ Fund := fun n => hUF n
  have hWl : ∀ n, W n ∈ lat := fun n => lat.add_mem (hTl n) (hUl n)
  have hqeq : ∀ n, pMap psi (q n) = pMap psi (pp n) := by
    intro n
    have hthis : q n = pp n + (-(T n)) := by simp [q, sub_eq_add_neg]
    rw [hthis]
    exact pMap_add_lat psi hper1 hper2 (lat.neg_mem (hTl n))
  have hreq : ∀ n, pMap psi (r n) = pMap psi (zz n) := by
    intro n
    have hthis : r n = zz n + (-(W n)) := by
      simp only [r, W, sub_eq_add_neg, neg_add]
      abel
    rw [hthis]
    exact pMap_add_lat psi hper1 hper2 (lat.neg_mem (hWl n))
  have hdist : ∀ n, dist (pMap psi (q n)) (pMap psi (r n)) < 1/((n:ℝ)+1) := by
    intro n
    rw [hqeq n, hreq n]
    exact (hpz n).1
  have hge : ∀ n m, m ∈ lat → Real.pi ≤ dist (r n) (q n + m) := by
    intro n m hm
    have hm' : m - T n + W n ∈ lat := by
      have hEq : m - T n + W n = (m + (-(T n))) - (-(W n)) := by abel
      rw [hEq]
      exact lat.sub_mem (lat.add_mem hm (lat.neg_mem (hTl n))) (lat.neg_mem (hWl n))
    have hh := (hpz n).2 (m - T n + W n) hm'
    have heq : dist (zz n) (pp n + (m - T n + W n)) = dist (r n) (q n + m) := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      simp only [r, q, W, sub_eq_add_neg]
      abel
    linarith [hh, heq]
  have hFcomp : IsCompact Fund := isCompact_Icc.prod isCompact_Icc
  obtain ⟨q0, hq0F, φ1, hφ1mono, hφ1⟩ := hFcomp.tendsto_subseq (fun n => hqF n)
  obtain ⟨r0, hr0F, φ2, hφ2mono, hφ2⟩ := hFcomp.tendsto_subseq (fun n => hrF (φ1 n))
  have hφ2at : Tendsto φ2 atTop atTop := hφ2mono.tendsto_atTop
  let φ : ℕ → ℕ := φ1 ∘ φ2
  have hφmono : StrictMono φ := hφ1mono.comp hφ2mono
  have hqtend : Tendsto (fun n => q (φ n)) atTop (𝓝 q0) := hφ1.comp hφ2at
  have hrtend : Tendsto (fun n => r (φ n)) atTop (𝓝 r0) := hφ2
  have hΨq : Tendsto (fun n => pMap psi (q (φ n))) atTop (𝓝 (pMap psi q0)) :=
    (hcont'.tendsto q0).comp hqtend
  have hΨr : Tendsto (fun n => pMap psi (r (φ n))) atTop (𝓝 (pMap psi r0)) :=
    (hcont'.tendsto r0).comp hrtend
  have hd0 : Tendsto (fun n => dist (pMap psi (q (φ n))) (pMap psi (r (φ n)))) atTop (𝓝 0) := by
    have hrho : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφmono.tendsto_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ : ℕ => (0:ℝ)) (h := fun n : ℕ => 1 / ((φ n : ℝ) + 1))
      tendsto_const_nhds hrho (fun n => dist_nonneg) (fun n => (hdist (φ n)).le)
  have hΨr' : Tendsto (fun n => pMap psi (r (φ n))) atTop (𝓝 (pMap psi q0)) :=
    hΨq.congr_dist hd0
  have hpq : pMap psi r0 = pMap psi q0 := tendsto_nhds_unique hΨr hΨr'
  have hm0 : r0 - q0 ∈ lat := (pMap_eq_iff psi hinj r0 q0).mp hpq
  have hdv : Tendsto (fun n => dist (r (φ n)) r0 + dist (q (φ n)) q0) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => dist (r (φ n)) r0) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.mp hrtend
    have h2 : Tendsto (fun n => dist (q (φ n)) q0) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.mp hqtend
    simpa using h1.add h2
  have hle : ∀ n, Real.pi ≤ dist (r (φ n)) r0 + dist (q (φ n)) q0 := by
    intro n
    have hbase : Real.pi ≤ dist (r (φ n)) (q (φ n) + (r0 - q0)) := hge (φ n) (r0 - q0) hm0
    have heq2 : dist r0 (q (φ n) + (r0 - q0)) = dist (q (φ n)) q0 := by
      rw [dist_eq_norm, dist_eq_norm]
      have : r0 - (q (φ n) + (r0 - q0)) = -(q (φ n) - q0) := by abel
      rw [this, norm_neg]
    have htri := dist_triangle (r (φ n)) r0 (q (φ n) + (r0 - q0))
    rw [heq2] at htri
    linarith
  have hconst : Tendsto (fun _ : ℕ => Real.pi) atTop (𝓝 Real.pi) := tendsto_const_nhds
  have hbad : Real.pi ≤ (0:ℝ) := le_of_tendsto_of_tendsto hconst hdv (Eventually.of_forall hle)
  linarith [Real.pi_pos]

/-- The union of the "non-central sheets" `ball (p + m, π)` over the nonzero period
vectors `m`. -/
def sheetUnion (p : ℝ × ℝ) : Set (ℝ × ℝ) :=
  ⋃ m : {m : ℝ × ℝ // m ∈ lat ∧ m ≠ 0}, Metric.ball (p + (m : ℝ × ℝ)) Real.pi

lemma isOpen_sheetUnion (p : ℝ × ℝ) : IsOpen (sheetUnion p) := by
  rw [sheetUnion]
  exact isOpen_iUnion (fun m => Metric.isOpen_ball)

/-- **The extrinsic systole bound.**  For a continuous, `2π`-periodic, modulo-`2π`
injective parametrisation `psi` of a torus there is `ρ > 0` such that the image of
every essential closed curve (one whose lift winds by a nonzero vector) has
diameter at least `ρ`. -/
theorem diameter_systole (psi : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hper1 : ∀ x y, psi (x + 2 * Real.pi) y = psi x y)
    (hper2 : ∀ x y, psi x (y + 2 * Real.pi) = psi x y)
    (hinj : ∀ x y x' y', psi x y = psi x' y' ↔
      (∃ k : ℤ, x = x' + k * (2 * Real.pi)) ∧ (∃ k : ℤ, y = y' + k * (2 * Real.pi)))
    (hcont : Continuous (fun p : ℝ × ℝ => psi p.1 p.2)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (lam : ℝ → EuclideanSpace ℝ (Fin 3)) (Λ : ℝ → ℝ × ℝ) (a b : ℤ),
      Continuous lam → Continuous Λ →
      (∀ t, psi (Λ t).1 (Λ t).2 = lam t) →
      (∀ t, Λ (t + 2 * Real.pi) = Λ t + (2 * Real.pi * a, 2 * Real.pi * b)) →
      (a, b) ≠ 0 →
      ρ ≤ Metric.diam (Set.range lam) := by
  obtain ⟨ρ, hρpos, hρ⟩ := exists_uniform_sheet_radius psi hper1 hper2 hinj hcont
  refine ⟨ρ, hρpos, ?_⟩
  intro lam Λ a b hlam hΛ hlift hper hab
  by_contra hlt
  have hlt' : Metric.diam (Set.range lam) < ρ := not_le.mp hlt
  have hlift' : ∀ t, pMap psi (Λ t) = lam t := fun t => hlift t
  have hperlat : (2 * Real.pi * (a:ℝ), 2 * Real.pi * (b:ℝ)) ∈ lat := ⟨a, b, by ext <;> ring⟩
  have hlamp : Function.Periodic lam (2 * Real.pi) := by
    intro t
    have hpm := pMap_add_lat psi hper1 hper2 hperlat (p := Λ t)
    rw [← hlift' (t + 2 * Real.pi), hper t, hpm, hlift' t]
  have hrange : Set.range lam = lam '' Set.Icc (0:ℝ) (2 * Real.pi) := by
    apply Set.Subset.antisymm
    · rintro x ⟨t, rfl⟩
      obtain ⟨k, hk⟩ := exists_int_sub_mem_Icc t
      refine ⟨t - (k:ℝ) * (2*Real.pi), hk, ?_⟩
      have hkk := (hlamp.int_mul k) (t - (k:ℝ) * (2*Real.pi))
      rw [show t - (k:ℝ) * (2*Real.pi) + (k:ℝ) * (2*Real.pi) = t by ring] at hkk
      exact hkk.symm
    · rintro x ⟨t, _ht, rfl⟩
      exact ⟨t, rfl⟩
  have hbdd : Bornology.IsBounded (Set.range lam) := by
    rw [hrange]
    exact ((isCompact_Icc (a := (0:ℝ)) (b := 2 * Real.pi)).image hlam).isBounded
  have hdist_lt : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi),
      dist (pMap psi (Λ t)) (pMap psi (Λ 0)) < ρ := by
    intro t ht
    rw [hlift' t, hlift' 0]
    have hle := Metric.dist_le_diam_of_mem hbdd
      (Set.mem_range_self (f := lam) t) (Set.mem_range_self (f := lam) 0)
    linarith [hle, hlt']
  have hdisj : Metric.ball (Λ 0) Real.pi ∩ sheetUnion (Λ 0) = ∅ := by
    rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_left]
    intro x hxU hxV
    rw [Metric.mem_ball] at hxU
    rw [sheetUnion] at hxV
    obtain ⟨m, hxV⟩ := Set.mem_iUnion.mp hxV
    rw [Metric.mem_ball] at hxV
    have hm : (m : ℝ × ℝ) ∈ lat := m.2.1
    have hmne : (m : ℝ × ℝ) ≠ 0 := m.2.2
    have hxU' : dist (Λ 0) x < Real.pi := by rw [dist_comm]; exact hxU
    have htri : dist (Λ 0) (Λ 0 + (m:ℝ × ℝ)) ≤
        dist (Λ 0) x + dist x (Λ 0 + (m:ℝ × ℝ)) := dist_triangle _ _ _
    have hnorm : 2 * Real.pi ≤ ‖(m : ℝ × ℝ)‖ := lat_norm_ge hm hmne
    have htrans : dist (Λ 0) (Λ 0 + (m:ℝ × ℝ)) = ‖(m:ℝ × ℝ)‖ := by
      rw [dist_eq_norm, show Λ 0 - (Λ 0 + (m:ℝ × ℝ)) = -(m:ℝ × ℝ) by abel, norm_neg]
    linarith [htri, hnorm, htrans, hxU', hxV, Real.pi_pos]
  have hCpre : IsPreconnected (Λ '' Set.Icc (0:ℝ) (2*Real.pi)) :=
    (isPreconnected_Icc (a := (0:ℝ)) (b := 2 * Real.pi)).image Λ hΛ.continuousOn
  have hCsub : Λ '' Set.Icc (0:ℝ) (2*Real.pi) ⊆
      Metric.ball (Λ 0) Real.pi ∪ sheetUnion (Λ 0) := by
    rintro x ⟨t, ht, rfl⟩
    obtain ⟨m, hml, hmD⟩ := hρ (Λ 0) (Λ t) (by rw [dist_comm]; exact hdist_lt t ht)
    rcases eq_or_ne m 0 with rfl | h0
    · left
      rw [Metric.mem_ball]
      simpa using hmD
    · right
      rw [sheetUnion]
      refine Set.mem_iUnion.mpr ⟨⟨m, hml, h0⟩, ?_⟩
      rw [Metric.mem_ball]
      simpa using hmD
  have hCU : Λ '' Set.Icc (0:ℝ) (2*Real.pi) ⊆ Metric.ball (Λ 0) Real.pi := by
    rcases (isPreconnected_iff_subset_of_disjoint.mp hCpre)
      (Metric.ball (Λ 0) Real.pi) (sheetUnion (Λ 0))
      Metric.isOpen_ball (isOpen_sheetUnion (Λ 0)) hCsub (by rw [hdisj, Set.inter_empty]) with h | h
    · exact h
    · exfalso
      have h0C : Λ 0 ∈ Λ '' Set.Icc (0:ℝ) (2*Real.pi) :=
        ⟨0, ⟨le_refl _, by linarith [Real.pi_pos]⟩, rfl⟩
      have h0U : Λ 0 ∈ Metric.ball (Λ 0) Real.pi := by
        rw [Metric.mem_ball]; simpa using Real.pi_pos
      have h0V : Λ 0 ∈ sheetUnion (Λ 0) := h h0C
      have hmem : Λ 0 ∈ Metric.ball (Λ 0) Real.pi ∩ sheetUnion (Λ 0) := ⟨h0U, h0V⟩
      rw [hdisj] at hmem
      exact hmem
  have hmem : Λ (2 * Real.pi) ∈ Metric.ball (Λ 0) Real.pi :=
    hCU ⟨2 * Real.pi, ⟨by linarith [Real.pi_pos], le_refl _⟩, rfl⟩
  rw [Metric.mem_ball] at hmem
  have hdisp : Λ (2 * Real.pi) = Λ 0 + (2 * Real.pi * (a:ℝ), 2 * Real.pi * (b:ℝ)) := by
    have := hper 0
    simpa using this
  have hpne : (2 * Real.pi * (a:ℝ), 2 * Real.pi * (b:ℝ)) ≠ 0 := by
    intro hh
    apply hab
    have h1 : (a:ℝ) = 0 := by
      have hf : 2 * Real.pi * (a:ℝ) = 0 := by simpa using (Prod.ext_iff.mp hh).1
      exact (mul_eq_zero.mp hf).resolve_left (by positivity : (2:ℝ) * Real.pi ≠ 0)
    have h2 : (b:ℝ) = 0 := by
      have hf : 2 * Real.pi * (b:ℝ) = 0 := by simpa using (Prod.ext_iff.mp hh).2
      exact (mul_eq_zero.mp hf).resolve_left (by positivity : (2:ℝ) * Real.pi ≠ 0)
    exact Prod.ext (Int.cast_eq_zero.mp h1) (Int.cast_eq_zero.mp h2)
  have hnorm := lat_norm_ge hperlat hpne
  have hdist2 : dist (Λ (2 * Real.pi)) (Λ 0) =
      ‖(2 * Real.pi * (a:ℝ), 2 * Real.pi * (b:ℝ))‖ := by
    rw [dist_eq_norm, hdisp]
    congr 1
    abel
  linarith [hnorm, hmem, hdist2, Real.pi_pos]

end

end Work.Geometry
