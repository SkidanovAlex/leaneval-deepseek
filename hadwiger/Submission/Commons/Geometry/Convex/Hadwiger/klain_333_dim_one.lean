import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.convexBody_interval_repr
import Submission.Commons.Geometry.Convex.Hadwiger.valuation_split_interval
import Submission.Commons.Geometry.Convex.Hadwiger.continuous_convexBody_smul

open Set
open Filter
open scoped Pointwise Topology

namespace Commons.Geometry.Convex.Hadwiger

/-- The canonical one-dimensional convex body `[0, 1]`. -/
noncomputable def klain333_unit : ConvexBody ℝ :=
  ⟨Set.Icc (0 : ℝ) 1, convex_Icc 0 1, isCompact_Icc, ⟨0, by norm_num⟩⟩

@[simp]
theorem klain333_unit_coe : (klain333_unit : Set ℝ) = Set.Icc (0 : ℝ) 1 :=
  rfl

/-- The canonical interval body `[a, b]` (for `a ≤ b`). -/
noncomputable def klain333_interval (a b : ℝ) (hab : a ≤ b) : ConvexBody ℝ :=
  ⟨Set.Icc a b, convex_Icc a b, isCompact_Icc, ⟨a, le_rfl, hab⟩⟩

@[simp]
theorem klain333_interval_coe (a b : ℝ) (hab : a ≤ b) :
    (klain333_interval a b hab : Set ℝ) = Set.Icc a b :=
  rfl

/-- Scalar multiples of `[0,1]` by a nonnegative `c` are exactly `[0, c]`. -/
lemma klain333_smul_Icc_unit (c : ℝ) (hc : 0 ≤ c) :
    c • (Set.Icc (0 : ℝ) 1 : Set ℝ) = Set.Icc 0 c := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_smul_set.mp hx with ⟨y, hy, hxy⟩
    have hy0 : (0 : ℝ) ≤ y := (Set.mem_Icc.mp hy).1
    have hy1 : y ≤ 1 := (Set.mem_Icc.mp hy).2
    have hxeq : c * y = x := by simpa [smul_eq_mul] using hxy
    constructor
    · nlinarith [mul_nonneg hc hy0, hxeq]
    · nlinarith [mul_le_mul_of_nonneg_left hy1 hc, hxeq]
  · intro hx
    have hx0 : 0 ≤ x := (Set.mem_Icc.mp hx).1
    have hx1 : x ≤ c := (Set.mem_Icc.mp hx).2
    rcases lt_or_eq_of_le hc with hcpos | hczero
    · refine Set.mem_smul_set.mpr ⟨x / c, ?_, ?_⟩
      · rw [Set.mem_Icc]
        constructor
        · exact div_nonneg hx0 (le_of_lt hcpos)
        · rw [div_le_one hcpos]
          exact hx1
      · rw [smul_eq_mul]
        rw [mul_comm]
        exact div_mul_cancel₀ x (ne_of_gt hcpos)
    · subst c
      have hx0' : x = 0 := by linarith
      refine Set.mem_smul_set.mpr ⟨0, ?_, ?_⟩
      · simp
      · simp [hx0']

theorem klain_333_dim_one
    (φ : ConvexBody ℝ → ℝ)
    (hcont : Continuous φ)
    (hadd : ∀ A B C D : ConvexBody ℝ,
        (A : Set ℝ) = (C : Set ℝ) ∪ (D : Set ℝ) →
        (B : Set ℝ) = (C : Set ℝ) ∩ (D : Set ℝ) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody ℝ, interior (K : Set ℝ) = ∅ → φ K = 0)
    (htrans : ∀ A B : ConvexBody ℝ, ∀ t : ℝ,
        (B : Set ℝ) = (fun x : ℝ => x + t) '' (A : Set ℝ) → φ A = φ B)
    (hunit : ∀ U : ConvexBody ℝ, (U : Set ℝ) = Set.Icc 0 1 → φ U = 0) :
    ∀ K : ConvexBody ℝ, φ K = 0 := by
  classical
  let G : ℝ → ℝ := fun t => φ (t • klain333_unit)
  have hGcont : Continuous G := by
    dsimp [G]
    exact hcont.comp (continuous_convexBody_smul (V := ℝ) klain333_unit)
  have hGadd : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → G (t + s) = G t + G s := by
    intro t s ht hs
    let Kcb : ConvexBody ℝ := klain333_interval t (t + s) (by linarith)
    have hKab : ((t + s) • klain333_unit : Set ℝ) = Set.Icc 0 (t + s) := by
      simpa using klain333_smul_Icc_unit (t + s) (add_nonneg ht hs)
    have hKac : (t • klain333_unit : Set ℝ) = Set.Icc 0 t := by
      simpa using klain333_smul_Icc_unit t ht
    have hsplit := valuation_split_interval φ hadd hsimple
        (a := 0) (b := t + s) (c := t) ht (by linarith)
        ((t + s) • klain333_unit) hKab
        (t • klain333_unit) hKac
        Kcb (by rfl)
    have htr : φ Kcb = φ (s • klain333_unit) := by
      apply htrans Kcb (s • klain333_unit) (-t)
      rw [klain333_interval_coe]
      have hLs : (s • klain333_unit : Set ℝ) = Set.Icc 0 s := by
        simpa using klain333_smul_Icc_unit s hs
      change s • (klain333_unit : Set ℝ) = (fun x : ℝ => x + (-t)) '' Set.Icc t (t + s)
      rw [hLs]
      rw [Set.image_add_const_Icc]
      congr 1 <;> linarith
    dsimp [G]
    calc
      φ ((t + s) • klain333_unit) = φ (t • klain333_unit) + φ Kcb := hsplit
      _ = φ (t • klain333_unit) + φ (s • klain333_unit) := by rw [htr]
  have hG0 : G 0 = 0 := by
    have h' : G 0 = G 0 + G 0 := by simpa using hGadd 0 0 le_rfl le_rfl
    linarith
  have hGone : G 1 = 0 := by
    dsimp [G]
    rw [one_smul]
    exact hunit klain333_unit (by rfl)
  have hGint : ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t → G ((k : ℝ) * t) = (k : ℝ) * G t := by
    intro k
    induction k with
    | zero =>
        intro t ht
        simp [hG0]
    | succ k ih =>
        intro t ht
        have h1 : G (((k + 1 : ℕ) : ℝ) * t) = G ((k : ℝ) * t + t) := by
          congr 1
          rw [Nat.cast_add, Nat.cast_one]
          ring
        have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by
          rw [Nat.cast_add, Nat.cast_one]
        rw [h1]
        rw [hGadd ((k : ℝ) * t) t (mul_nonneg (Nat.cast_nonneg k) ht) ht]
        rw [ih t ht]
        rw [hcast]
        ring
  have hGzero_nat : ∀ m n : ℕ, n ≠ 0 → G ((m : ℝ) / (n : ℝ)) = 0 := by
    intro m n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have ht : 0 ≤ (m : ℝ) / (n : ℝ) :=
      div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)
    have h1 : G ((n : ℝ) * ((m : ℝ) / (n : ℝ))) = (n : ℝ) * G ((m : ℝ) / (n : ℝ)) :=
      hGint n ((m : ℝ) / (n : ℝ)) ht
    have hnfac : (n : ℝ) * ((m : ℝ) / (n : ℝ)) = (m : ℝ) := by
      field_simp [hnR]
    have hm : G ((m : ℝ)) = (m : ℝ) * G 1 := by
      simpa using hGint m (1 : ℝ) (by norm_num)
    have hm0 : G ((m : ℝ)) = 0 := by
      rw [hm]
      simp [hGone]
    have hmain : (n : ℝ) * G ((m : ℝ) / (n : ℝ)) = 0 := by
      rw [← h1, hnfac]
      exact hm0
    exact (mul_eq_zero.mp hmain).resolve_left hnR
  have hGzero : ∀ t : ℝ, 0 ≤ t → G t = 0 := by
    intro t ht
    let q : ℕ → ℝ := fun n => (⌊t * (n : ℝ)⌋₊ : ℝ) / (n : ℝ)
    have hq_tend : Tendsto q atTop (𝓝 t) := by
      dsimp [q]
      have hbase : Tendsto (fun x : ℝ => (⌊t * x⌋₊ : ℝ) / x) atTop (𝓝 t) :=
        tendsto_nat_floor_mul_div_atTop (a := t) ht
      exact hbase.comp tendsto_natCast_atTop_atTop
    have hqzero : ∀ n : ℕ, n ≠ 0 → G (q n) = 0 := by
      intro n hn
      dsimp [q]
      exact hGzero_nat ⌊t * (n : ℝ)⌋₊ n hn
    have hGseq : Tendsto (fun n : ℕ => G (q n)) atTop (𝓝 (G t)) :=
      hGcont.continuousAt.tendsto.comp hq_tend
    have hev : (fun n : ℕ => G (q n)) =ᶠ[atTop] (fun n : ℕ => (0 : ℝ)) := by
      rw [Filter.EventuallyEq]
      exact Filter.eventually_atTop.2 ⟨1, fun n hn1 => hqzero n (by omega)⟩
    have hGseq0 : Tendsto (fun n : ℕ => G (q n)) atTop (𝓝 0) :=
      Filter.Tendsto.congr' hev.symm (tendsto_const_nhds (x := (0 : ℝ)) (α := ℕ))
    exact tendsto_nhds_unique hGseq hGseq0
  intro K
  rcases convexBody_interval_repr K with ⟨a, b, hab, hKab⟩
  let L : ℝ := b - a
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hphi : φ K = φ (L • klain333_unit) := by
    apply htrans K (L • klain333_unit) (-a)
    rw [hKab]
    have hLHS : (L • klain333_unit : Set ℝ) = Set.Icc 0 L := by
      simpa using klain333_smul_Icc_unit L hL
    change L • (klain333_unit : Set ℝ) = (fun x : ℝ => x + (-a)) '' Set.Icc a b
    rw [hLHS]
    have himg : (fun x : ℝ => x + (-a)) '' Set.Icc a b = Set.Icc 0 L := by
      rw [Set.image_add_const_Icc]
      congr 1
      ring
    exact himg.symm
  calc
    φ K = φ (L • klain333_unit) := hphi
    _ = G L := by rfl
    _ = 0 := hGzero L hL

end Commons.Geometry.Convex.Hadwiger
