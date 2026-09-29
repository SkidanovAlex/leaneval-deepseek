import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.buQWhs
import Submission.Work.Kernel.Raw
import Submission.Work.Resample.auKit
import Submission.Work.Fx.norm_tdiv_sub_div_lt

/-!
# `Work.Resample.buQWstepKit`: list-level analysis of one Neumann round

The word `buQWstep` computes one round of the truncated Gaussian convolution as a fold over the
column list `buColsN Wt s (egM p α)` (paper Lemma 4.11), followed by the division by `2^p` and the
signed accumulation into the Neumann sum.

This module fixes the *list-level* partial fold `buPFold`, the partial row sums `buRowS`, and the
elementary list/norm facts about `buAddV`, `buMulCol`, `buRot`, `buTdivV`, `buColL` that the
correctness and the disc bounds of that word need.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-! ## Gaussian integers as complex numbers -/

/-- The Gaussian integer `z` as a complex number. -/
def gz (z : ℤ × ℤ) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

theorem gz_real (z : ℤ × ℤ) : gz z = (((z.1 : ℝ) : ℂ) + ((z.2 : ℝ) : ℂ) * Complex.I) := by
  simp only [gz]; push_cast; ring

theorem gz_sq (z : ℤ × ℤ) : ‖gz z‖ ^ 2 = (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 := by
  rw [gz_real, Complex.sq_norm, Complex.normSq_add_mul_I]

theorem gz_add (x y : ℤ × ℤ) : gz (x.1 + y.1, x.2 + y.2) = gz x + gz y := by
  simp only [gz]; push_cast; ring

theorem gz_smul (c : ℤ) (z : ℤ × ℤ) : gz (c * z.1, c * z.2) = (c : ℂ) * gz z := by
  simp only [gz]; push_cast; ring

/-- The disc condition is exactly `‖gz z‖ ≤ B`. -/
theorem buIn_iff (B : ℕ) (z : ℤ × ℤ) : buIn B z ↔ ‖gz z‖ ≤ (B : ℝ) := by
  rw [buIn]
  have hcast : ((z.1 ^ 2 + z.2 ^ 2 : ℤ) : ℝ) = (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 := by
    push_cast; ring
  have hBc : (((B : ℤ) ^ 2 : ℤ) : ℝ) = (B : ℝ) ^ 2 := by push_cast; ring
  constructor
  · intro h
    have h1 : ((z.1 ^ 2 + z.2 ^ 2 : ℤ) : ℝ) ≤ (((B : ℤ) ^ 2 : ℤ) : ℝ) := by exact_mod_cast h
    rw [hcast, hBc] at h1
    have h2 : ‖gz z‖ ^ 2 ≤ (B : ℝ) ^ 2 := by rw [gz_sq]; exact h1
    nlinarith [norm_nonneg (gz z), (by positivity : (0 : ℝ) ≤ (B : ℝ))]
  · intro h
    have h2 : (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 ≤ (B : ℝ) ^ 2 := by
      rw [← gz_sq]; nlinarith [norm_nonneg (gz z), (by positivity : (0 : ℝ) ≤ (B : ℝ))]
    have h1 : ((z.1 ^ 2 + z.2 ^ 2 : ℤ) : ℝ) ≤ (((B : ℤ) ^ 2 : ℤ) : ℝ) := by
      rw [hcast, hBc]; exact h2
    exact_mod_cast h1

/-- `buIn C z` holds as soon as `‖gz z‖ ≤ C`. -/
theorem buIn_of_gz_le {C : ℕ} {z : ℤ × ℤ} (h : ‖gz z‖ ≤ (C : ℝ)) : buIn C z :=
  (buIn_iff C z).mpr h

theorem buInV_iff (B : ℕ) (v : List (ℤ × ℤ)) :
    buInV B v ↔ ∀ z ∈ v, ‖gz z‖ ≤ (B : ℝ) := by
  unfold buInV
  constructor
  · intro h z hz; exact (buIn_iff B z).mp (h z hz)
  · intro h z hz; exact (buIn_iff B z).mpr (h z hz)

/-- Adding two vectors lying in discs adds the radii. -/
theorem buInV_buAddV {B B' : ℕ} :
    ∀ {a b : List (ℤ × ℤ)}, buInV B a → buInV B' b → buInV (B + B') (buAddV a b)
  | [], _, _, _ => by simp [buAddV, buInV]
  | _, [], _, _ => by simp [buAddV, buInV]
  | x :: xs, y :: ys, ha, hb => by
      rw [buAddV]
      intro z hz
      rcases List.mem_cons.mp hz with h | h
      · subst h
        exact buIn_add (ha x (by simp)) (hb y (by simp))
      · exact buInV_buAddV (fun z hz => ha z (List.mem_cons_of_mem _ hz))
          (fun z hz => hb z (List.mem_cons_of_mem _ hz)) z h

/-- Scalar multiplication by `±1` preserves the disc radius. -/
theorem buInV_buSMulV {B : ℕ} {c : ℤ} (hc : c = 1 ∨ c = -1) {v : List (ℤ × ℤ)}
    (h : buInV B v) : buInV B (buSMulV c v) := by
  rw [buInV_iff] at h ⊢
  intro z hz
  rw [buSMulV, List.mem_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  have hy' : ‖gz y‖ ≤ (B : ℝ) := h y hy
  rcases hc with hc | hc <;> subst hc
  · simpa using hy'
  · have hgz : gz (-1 * y.1, -1 * y.2) = -gz y := by rw [gz_smul]; norm_num
    rw [hgz, norm_neg]; exact hy'

/-! ## elementary list facts about the vector operations -/

theorem buAddV_length (a b : List (ℤ × ℤ)) : (buAddV a b).length = min a.length b.length := by
  induction a generalizing b with
  | nil => simp [buAddV]
  | cons x xs ih =>
      cases b with
      | nil => simp [buAddV]
      | cons y ys => simp [buAddV, ih]

theorem buMulCol_length (w : List ℤ) (v : List (ℤ × ℤ)) :
    (buMulCol w v).length = min w.length v.length := by
  simp [buMulCol]

theorem buRot_length (k : ℕ) (v : List (ℤ × ℤ)) : (buRot k v).length = v.length := by
  simp only [buRot, List.length_append, List.length_drop, List.length_take]
  omega

theorem buTdivV_length (p : ℕ) (v : List (ℤ × ℤ)) : (buTdivV p v).length = v.length := by
  simp [buTdivV]

theorem buColL_length (Wt : ℤ → ℤ → ℤ) (s : ℕ) (h : ℤ) : (buColL Wt s h).length = s := by
  simp [buColL]

theorem buColL_getD (Wt : ℤ → ℤ → ℤ) (s : ℕ) (h : ℤ) (ℓ : ℕ) (hℓ : ℓ < s) :
    (buColL Wt s h).getD ℓ 0 = Wt (ℓ : ℤ) h := by
  rw [buColL, List.getD_eq_getElem _ _ (by simpa [buColL] using hℓ)]
  simp only [List.getElem_ofFn]

theorem buAddV_getD : ∀ (a b : List (ℤ × ℤ)) (i : ℕ), i < a.length → i < b.length →
    (buAddV a b).getD i (0, 0)
      = ((a.getD i (0, 0)).1 + (b.getD i (0, 0)).1, (a.getD i (0, 0)).2 + (b.getD i (0, 0)).2)
  | [], v, i, h, _ => by simp at h
  | _, [], i, _, h => by simp at h
  | _ :: as, _ :: bs, 0, _, _ => rfl
  | _ :: as, _ :: bs, i + 1, h1, h2 => by
      simp only [buAddV, List.getD_cons_succ, List.length_cons] at *
      exact buAddV_getD as bs i (by omega) (by omega)

theorem buMulCol_getD : ∀ (w : List ℤ) (v : List (ℤ × ℤ)) (i : ℕ), i < w.length → i < v.length →
    (buMulCol w v).getD i (0, 0)
      = (w.getD i 0 * (v.getD i (0, 0)).1, w.getD i 0 * (v.getD i (0, 0)).2)
  | [], v, i, h, _ => by simp at h
  | _, [], i, _, h => by simp at h
  | _ :: ws, _ :: vs, 0, _, _ => rfl
  | _ :: ws, _ :: vs, i + 1, h1, h2 => by
      simp only [buMulCol, List.zip_cons_cons, List.map_cons, List.getD_cons_succ,
        List.length_cons] at *
      exact buMulCol_getD ws vs i (by omega) (by omega)

theorem buTdivV_getD : ∀ (p : ℕ) (v : List (ℤ × ℤ)) (i : ℕ), i < v.length →
    (buTdivV p v).getD i (0, 0)
      = (Int.tdiv (v.getD i (0, 0)).1 ((2 : ℤ) ^ p), Int.tdiv (v.getD i (0, 0)).2 ((2 : ℤ) ^ p))
  | _, [], i, h => by simp at h
  | p, _ :: vs, 0, _ => rfl
  | p, _ :: vs, i + 1, h => by
      simp only [buTdivV, List.map_cons, List.getD_cons_succ, List.length_cons] at *
      exact buTdivV_getD p vs i (by omega)

/-- Reading of `drop`. -/
theorem getD_drop_eq : ∀ (v : List (ℤ × ℤ)) (k i : ℕ),
    (v.drop k).getD i (0, 0) = v.getD (i + k) (0, 0)
  | [], k, i => by simp
  | _ :: t, 0, i => by simp
  | a :: t, k + 1, i => by
      have h1 : i + (k + 1) = (i + k) + 1 := by omega
      rw [List.drop_succ_cons, getD_drop_eq t k i, h1, List.getD_cons_succ]

/-- Reading of `take`. -/
theorem getD_take_eq : ∀ (v : List (ℤ × ℤ)) (k i : ℕ), i < k →
    (v.take k).getD i (0, 0) = v.getD i (0, 0)
  | [], k, i, _ => by simp
  | _ :: t, 0, i, h => by simp at h
  | _ :: t, k + 1, 0, _ => by simp
  | _ :: t, k + 1, i + 1, h => by
      simp only [List.take_succ_cons, List.getD_cons_succ]
      exact getD_take_eq t k i (by omega)

/-- Reading the rotation: entry `ℓ` of `buRot k v` is entry `ℓ + k` modulo the length. -/
theorem buRot_getD (k : ℕ) (v : List (ℤ × ℤ)) (ℓ : ℕ) (hℓ : ℓ < v.length)
    (hk : k ≤ v.length) :
    (buRot k v).getD ℓ (0, 0) = v.getD ((ℓ + k) % v.length) (0, 0) := by
  have hn : 0 < v.length := lt_of_le_of_lt (Nat.zero_le _) hℓ
  rw [buRot]
  by_cases h : ℓ < v.length - k
  · rw [List.getD_append _ _ _ _ (by rw [List.length_drop]; omega), getD_drop_eq]
    congr 1
    rw [Nat.mod_eq_of_lt]
    omega
  · rw [List.getD_append_right _ _ _ _ (by rw [List.length_drop]; omega), List.length_drop]
    have h2 : ℓ - (v.length - k) < k := by omega
    rw [getD_take_eq v k (ℓ - (v.length - k)) h2]
    congr 1
    rw [show ℓ + k = (ℓ + k - v.length) + v.length by omega]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt]
    · omega
    · omega

/-- Reduction of the shift modulo `s` commutes with the shift of the index. -/
theorem buIdx_eq (s : ℕ) (hs : 0 < s) (ℓ : ℕ) (h : ℤ) :
    (ℓ + (h % (s : ℤ)).toNat) % s = (((ℓ : ℤ) + h) % s).toNat := by
  have hsZ : (0 : ℤ) < (s : ℤ) := by exact_mod_cast hs
  have h0 : 0 ≤ h % (s : ℤ) := Int.emod_nonneg h (by omega)
  have hk : (((h % (s : ℤ)).toNat : ℕ) : ℤ) = h % (s : ℤ) := Int.toNat_of_nonneg h0
  have hcast : (((ℓ + (h % (s : ℤ)).toNat) : ℕ) : ℤ) = (ℓ : ℤ) + h % (s : ℤ) := by
    push_cast; rw [hk]
  have hnn : 0 ≤ ((ℓ : ℤ) + h) % s := Int.emod_nonneg _ (by omega)
  have hmod : ((ℓ : ℤ) + h % (s : ℤ)) % (s : ℤ) = ((ℓ : ℤ) + h) % (s : ℤ) := by
    have h1 : ((ℓ : ℤ) : ℤ) ≡ (ℓ : ℤ) [ZMOD (s : ℤ)] := Int.ModEq.refl _
    exact Int.ModEq.add h1 (Int.mod_modEq h (s : ℤ))
  have hgoal : ((((ℓ + (h % (s : ℤ)).toNat) % s : ℕ)) : ℤ)
      = (((((ℓ : ℤ) + h) % s).toNat : ℕ) : ℤ) := by
    rw [Int.natCast_mod, hcast, hmod, Int.toNat_of_nonneg hnn]
  exact_mod_cast hgoal

/-! ## the partial fold and the row sums -/

/-- The partial fold of the round over the first `i` columns. -/
def buPFold (Wt : ℤ → ℤ → ℤ) (s m : ℕ) (v : List (ℤ × ℤ)) (i : ℕ) : List (ℤ × ℤ) :=
  List.foldl (fun acc hc => buAddV acc (buMulCol hc.2 (buRot hc.1 v)))
    (List.replicate s (0, 0)) ((buColsN Wt s m).take i)

/-- The rotation amount of the `i`-th column (the shift reduced modulo `s`). -/
def buKk (s m : ℕ) (i : ℕ) : ℕ := ((egHs m).getD i 0 % (s : ℤ)).toNat

/-- The partial row sum: the total mass of the first `i` columns in row `ℓ`. -/
noncomputable def buRowS (Wt : ℤ → ℤ → ℤ) (m : ℕ) (ℓ : ℤ) (i : ℕ) : ℝ :=
  (((egHs m).take i).map (fun h => |(Wt ℓ h : ℝ)|)).sum

theorem buColsN_length (Wt : ℤ → ℤ → ℤ) (s m : ℕ) : (buColsN Wt s m).length = 2 * m := by
  simp [buColsN, buColsL, buQWhs_length]

theorem buColsN_getD (Wt : ℤ → ℤ → ℤ) (s m i : ℕ) (h : i < 2 * m) :
    (buColsN Wt s m).getD i (0, []) = (buKk s m i, buColL Wt s ((egHs m).getD i 0)) := by
  have h1 : i < (buColsL Wt s m).length := by
    simp [buColsL, buQWhs_length]; omega
  have h2 : i < (egHs m).length := by rw [buQWhs_length]; omega
  have hlen : i < (buColsN Wt s m).length := by
    simp [buColsN, buColsL, buQWhs_length]; omega
  rw [List.getD_eq_getElem _ _ hlen]
  simp only [buColsN, buColsL, List.getElem_map]
  rw [← List.getD_eq_getElem _ _ h2]
  rfl

theorem buPFold_zero (Wt : ℤ → ℤ → ℤ) (s m : ℕ) (v : List (ℤ × ℤ)) :
    buPFold Wt s m v 0 = List.replicate s (0, 0) := by
  simp [buPFold]

theorem buPFold_succ (Wt : ℤ → ℤ → ℤ) (s m : ℕ) (v : List (ℤ × ℤ)) (i : ℕ)
    (h : i < (buColsN Wt s m).length) :
    buPFold Wt s m v (i + 1)
      = buAddV (buPFold Wt s m v i)
          (buMulCol (buColL Wt s ((egHs m).getD i 0)) (buRot (buKk s m i) v)) := by
  have hstep : (buColsN Wt s m).take (i + 1) = (buColsN Wt s m).take i ++ [(buColsN Wt s m)[i]] :=
    (List.take_concat_get' _ _ h).symm
  have hget : (buColsN Wt s m)[i] = (buKk s m i, buColL Wt s ((egHs m).getD i 0)) := by
    rw [← List.getD_eq_getElem _ _ h]
    exact buColsN_getD Wt s m i (by simpa [buColsN_length] using h)
  rw [buPFold, buPFold, hstep, hget, List.foldl_append]
  rfl

theorem buPFold_length (Wt : ℤ → ℤ → ℤ) (s m : ℕ) (v : List (ℤ × ℤ)) (hv : v.length = s) :
    ∀ i, i ≤ (buColsN Wt s m).length → (buPFold Wt s m v i).length = s
  | 0, _ => by simp [buPFold, hv]
  | i + 1, hi => by
      have hi' : i < (buColsN Wt s m).length := by omega
      rw [buPFold_succ Wt s m v i hi', buAddV_length, buPFold_length Wt s m v hv i (le_of_lt hi'),
        buMulCol_length, buColL_length, buRot_length, hv]
      omega

theorem buRowS_zero (Wt : ℤ → ℤ → ℤ) (m : ℕ) (ℓ : ℤ) : buRowS Wt m ℓ 0 = 0 := by
  simp [buRowS]

theorem buRowS_succ (Wt : ℤ → ℤ → ℤ) (m : ℕ) (ℓ : ℤ) (i : ℕ) (h : i < (egHs m).length) :
    buRowS Wt m ℓ (i + 1) = buRowS Wt m ℓ i + |(Wt ℓ ((egHs m).getD i 0) : ℝ)| := by
  have htake : (egHs m).take (i + 1) = (egHs m).take i ++ [(egHs m)[i]] :=
    (List.take_concat_get' _ _ h).symm
  have hget : (egHs m)[i] = (egHs m).getD i 0 := (List.getD_eq_getElem _ _ h).symm
  rw [buRowS, buRowS, htake, List.map_append, List.sum_append, hget]
  simp

theorem sum_toFinset {α : Type} [DecidableEq α] {M : Type} [AddCommMonoid M]
    {l : List α} (hn : l.Nodup) (f : α → M) : (l.map f).sum = ∑ x ∈ l.toFinset, f x := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have hnt : t.Nodup := (List.nodup_cons.mp hn).2
      have ha : a ∉ t := (List.nodup_cons.mp hn).1
      have hthis : ∑ x ∈ (a :: t).toFinset, f x = f a + ∑ x ∈ t.toFinset, f x := by
        rw [List.toFinset_cons]
        exact Finset.sum_insert (by simpa [List.mem_toFinset] using ha)
      rw [hthis, List.map_cons, List.sum_cons, ih hnt]

theorem buRowS_full (Wt : ℤ → ℤ → ℤ) (m : ℕ) (ℓ : ℤ) :
    buRowS Wt m ℓ (2 * m) = ∑ h ∈ egHset m, |(Wt ℓ h : ℝ)| := by
  have htake : (egHs m).take (2 * m) = egHs m :=
    List.take_of_length_le (by rw [buQWhs_length])
  rw [buRowS, htake, sum_toFinset (buQWhs_nodup m)]
  congr 1
  exact (buQWhs m).1

/-! ## the row bound along the fold -/

theorem buPFold_gz_le (Wt : ℤ → ℤ → ℤ) (s m : ℕ) (B : ℕ) (v : List (ℤ × ℤ))
    (hv : v.length = s) (hB : ∀ z ∈ v, ‖gz z‖ ≤ (B : ℝ)) :
    ∀ i, i ≤ (buColsN Wt s m).length → ∀ ℓ < s,
      ‖gz ((buPFold Wt s m v i).getD ℓ (0, 0))‖ ≤ buRowS Wt m (ℓ : ℤ) i * (B : ℝ)
  | 0, _, ℓ, hℓ => by
      rw [buPFold_zero, buRowS_zero, zero_mul,
        List.getD_eq_getElem _ _ (by simpa [List.length_replicate] using hℓ),
        List.getElem_replicate]
      simp [gz]
  | i + 1, hi, ℓ, hℓ => by
      have hi' : i < (buColsN Wt s m).length := by omega
      have him : i < (egHs m).length := by rw [buColsN_length] at hi'; rw [buQWhs_length]; omega
      have hA : (buPFold Wt s m v i).length = s :=
        buPFold_length Wt s m v hv i (le_of_lt hi')
      have hcol : (buColL Wt s ((egHs m).getD i 0)).length = s := buColL_length _ _ _
      have hrot : (buRot (buKk s m i) v).length = s := by rw [buRot_length, hv]
      have hk : buKk s m i ≤ v.length := by
        rw [buKk, hv]
        have h1 : ((((egHs m).getD i 0 % (s : ℤ)).toNat : ℕ) : ℤ) = (egHs m).getD i 0 % (s : ℤ) :=
          Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
        have h2 : (egHs m).getD i 0 % (s : ℤ) < (s : ℤ) := Int.emod_lt_of_pos _ (by omega)
        omega
      rw [buPFold_succ Wt s m v i hi']
      have hadd := buAddV_getD (buPFold Wt s m v i)
        (buMulCol (buColL Wt s ((egHs m).getD i 0)) (buRot (buKk s m i) v)) ℓ
        (by rw [hA]; omega) (by rw [buMulCol_length, hcol, hrot]; omega)
      rw [hadd]
      have hmc := buMulCol_getD (buColL Wt s ((egHs m).getD i 0)) (buRot (buKk s m i) v) ℓ
        (by rw [hcol]; omega) (by rw [hrot]; omega)
      rw [hmc, gz_add, gz_smul]
      have hrowi : ‖gz ((buPFold Wt s m v i).getD ℓ (0, 0))‖
          ≤ buRowS Wt m (ℓ : ℤ) i * (B : ℝ) :=
        buPFold_gz_le Wt s m B v hv hB i (le_of_lt hi') ℓ hℓ
      have hcolv : (buColL Wt s ((egHs m).getD i 0)).getD ℓ 0 = Wt (ℓ : ℤ) ((egHs m).getD i 0) :=
        buColL_getD _ _ _ ℓ hℓ
      have hrv : ‖gz ((buRot (buKk s m i) v).getD ℓ (0, 0))‖ ≤ (B : ℝ) := by
        have hrotg : (buRot (buKk s m i) v).getD ℓ (0, 0)
            = v.getD ((ℓ + buKk s m i) % v.length) (0, 0) :=
          buRot_getD _ _ _ (by omega) hk
        rw [hrotg]
        have hidx : (ℓ + buKk s m i) % v.length
            = (((ℓ : ℤ) + (egHs m).getD i 0) % (s : ℤ)).toNat := by
          rw [hv, buKk]
          exact buIdx_eq s (by omega) ℓ ((egHs m).getD i 0)
        rw [hidx]
        have hlt : (((ℓ : ℤ) + (egHs m).getD i 0) % (s : ℤ)).toNat < v.length := by
          rw [hv]
          have h1 : (0 : ℤ) ≤ ((ℓ : ℤ) + (egHs m).getD i 0) % (s : ℤ) :=
            Int.emod_nonneg _ (by omega)
          have h2 : ((ℓ : ℤ) + (egHs m).getD i 0) % (s : ℤ) < (s : ℤ) :=
            Int.emod_lt_of_pos _ (by omega)
          have h3 : ((((ℓ : ℤ) + (egHs m).getD i 0) % (s : ℤ)).toNat : ℤ)
              = ((ℓ : ℤ) + (egHs m).getD i 0) % (s : ℤ) := Int.toNat_of_nonneg h1
          omega
        rw [List.getD_eq_getElem _ _ hlt]
        exact hB _ (List.getElem_mem hlt)
      calc ‖gz ((buPFold Wt s m v i).getD ℓ (0, 0))
              + ((buColL Wt s ((egHs m).getD i 0)).getD ℓ 0 : ℂ)
                * gz ((buRot (buKk s m i) v).getD ℓ (0, 0))‖
          ≤ ‖gz ((buPFold Wt s m v i).getD ℓ (0, 0))‖
            + ‖((buColL Wt s ((egHs m).getD i 0)).getD ℓ 0 : ℂ)
                * gz ((buRot (buKk s m i) v).getD ℓ (0, 0))‖ := norm_add_le _ _
        _ = ‖gz ((buPFold Wt s m v i).getD ℓ (0, 0))‖
            + |((buColL Wt s ((egHs m).getD i 0)).getD ℓ 0 : ℝ)|
              * ‖gz ((buRot (buKk s m i) v).getD ℓ (0, 0))‖ := by
              rw [norm_mul, Complex.norm_intCast]
        _ ≤ buRowS Wt m (ℓ : ℤ) i * (B : ℝ)
            + |(Wt (ℓ : ℤ) ((egHs m).getD i 0) : ℝ)| * (B : ℝ) := by
              rw [hcolv]
              exact add_le_add hrowi (mul_le_mul_of_nonneg_left hrv (abs_nonneg _))
        _ = buRowS Wt m (ℓ : ℤ) (i + 1) * (B : ℝ) := by
              rw [buRowS_succ Wt m (ℓ : ℤ) i him]; ring

/-- The round as the fold plus the division by `2^p`. -/
theorem buRoundL_eq_pfold (Wt : ℤ → ℤ → ℤ) (p s m : ℕ) (v : List (ℤ × ℤ)) :
    buRoundL Wt p s m v = buTdivV p (buPFold Wt s m v (2 * m)) := by
  rw [buRoundL, buPFold]
  congr 1
  rw [List.take_of_length_le (by rw [buColsN_length])]

/-- Dividing a Gaussian integer by `2^p` moves it by less than `√2` in the fixed-point metric. -/
theorem gz_tdiv_key (w : ℤ × ℤ) (p : ℕ) :
    ‖gz (Int.tdiv w.1 ((2 : ℤ) ^ p), Int.tdiv w.2 ((2 : ℤ) ^ p))
        - gz w / (((2 : ℤ) ^ p : ℤ) : ℂ)‖ < Real.sqrt 2 := by
  have h := Work.Fx.norm_tdiv_sub_div_lt (A := w.1) (B := w.2) (b := 2 ^ p) (by positivity)
  have hZ : ((2 : ℤ) ^ p) = (((2 ^ p : ℕ)) : ℤ) := by push_cast; ring
  rw [hZ]
  have hse : gz (Int.tdiv w.1 (((2 ^ p : ℕ)) : ℤ), Int.tdiv w.2 (((2 ^ p : ℕ)) : ℤ))
        - gz w / ((((2 ^ p : ℕ) : ℤ)) : ℂ)
      = ((Int.tdiv w.1 (((2 ^ p : ℕ)) : ℤ) : ℂ)
          + (Int.tdiv w.2 (((2 ^ p : ℕ)) : ℤ) : ℂ) * Complex.I
          - (((w.1 : ℝ) : ℂ) + ((w.2 : ℝ) : ℂ) * Complex.I) / ((2 ^ p : ℕ) : ℂ)) := by
    rw [gz, gz]; push_cast; ring
  rw [hse]
  exact h

/-- The entries of the round: the fold bound plus the truncation error `< √2`. -/
theorem buRoundL_gz_le (Wt : ℤ → ℤ → ℤ) (p s m : ℕ) (B : ℕ) (v : List (ℤ × ℤ))
    (hv : v.length = s) (hB : ∀ z ∈ v, ‖gz z‖ ≤ (B : ℝ)) (ℓ : ℕ) (hℓ : ℓ < s) :
    ‖gz ((buRoundL Wt p s m v).getD ℓ (0, 0))‖
      ≤ (buRowS Wt m (ℓ : ℤ) (2 * m) * (B : ℝ)) / (2 : ℝ) ^ p + Real.sqrt 2 := by
  have hlen : (buPFold Wt s m v (2 * m)).length = s :=
    buPFold_length Wt s m v hv (2 * m) (by rw [buColsN_length])
  set z : ℤ × ℤ := (buPFold Wt s m v (2 * m)).getD ℓ (0, 0) with hz
  have htd : (buRoundL Wt p s m v).getD ℓ (0, 0)
      = (Int.tdiv z.1 ((2 : ℤ) ^ p), Int.tdiv z.2 ((2 : ℤ) ^ p)) := by
    rw [buRoundL_eq_pfold]
    have h := buTdivV_getD p (buPFold Wt s m v (2 * m)) ℓ (by rw [hlen]; exact hℓ)
    rw [h]
  rw [htd]
  have hkey := gz_tdiv_key z p
  have htri : ‖gz (Int.tdiv z.1 ((2 : ℤ) ^ p), Int.tdiv z.2 ((2 : ℤ) ^ p))‖
      ≤ ‖gz (Int.tdiv z.1 ((2 : ℤ) ^ p), Int.tdiv z.2 ((2 : ℤ) ^ p))
            - gz z / (((2 : ℤ) ^ p : ℤ) : ℂ)‖
        + ‖gz z / (((2 : ℤ) ^ p : ℤ) : ℂ)‖ := by
    have h := norm_add_le (gz (Int.tdiv z.1 ((2 : ℤ) ^ p), Int.tdiv z.2 ((2 : ℤ) ^ p))
        - gz z / (((2 : ℤ) ^ p : ℤ) : ℂ)) (gz z / (((2 : ℤ) ^ p : ℤ) : ℂ))
    rwa [sub_add_cancel] at h
  have hdiv : ‖gz z / (((2 : ℤ) ^ p : ℤ) : ℂ)‖ = ‖gz z‖ / (2 : ℝ) ^ p := by
    rw [norm_div]
    congr 1
    rw [show (((2 : ℤ) ^ p : ℤ) : ℂ) = (((2 ^ p : ℕ)) : ℂ) by push_cast; ring,
      Complex.norm_natCast]
    push_cast
    ring
  have hfold : ‖gz z‖ ≤ buRowS Wt m (ℓ : ℤ) (2 * m) * (B : ℝ) := by
    rw [hz]
    exact buPFold_gz_le Wt s m B v hv hB (2 * m) (by rw [buColsN_length]) ℓ hℓ
  calc ‖gz (Int.tdiv z.1 ((2 : ℤ) ^ p), Int.tdiv z.2 ((2 : ℤ) ^ p))‖
      ≤ Real.sqrt 2 + buRowS Wt m (ℓ : ℤ) (2 * m) * (B : ℝ) / (2 : ℝ) ^ p := by
        rw [hdiv] at htri
        have h1 : ‖gz z‖ / (2 : ℝ) ^ p
            ≤ buRowS Wt m (ℓ : ℤ) (2 * m) * (B : ℝ) / (2 : ℝ) ^ p :=
          div_le_div_of_nonneg_right hfold (by positivity)
        have h2 : ‖gz (Int.tdiv z.1 ((2 : ℤ) ^ p), Int.tdiv z.2 ((2 : ℤ) ^ p)) - gz z
            / (((2 : ℤ) ^ p : ℤ) : ℂ)‖ ≤ Real.sqrt 2 := le_of_lt hkey
        linarith [htri, h1, h2]
    _ = buRowS Wt m (ℓ : ℤ) (2 * m) * (B : ℝ) / (2 : ℝ) ^ p + Real.sqrt 2 := by ring


/-! ## size and arithmetic lemmas (adapted from `buQWrounds`) -/

theorem buQT_take_succ {α : Type} [Inhabited α] (l : List α) (i : ℕ) (hi : i < l.length) :
    l.take (i + 1) = l.take i ++ [l.getD i default] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases i with
    | zero => rfl
    | succ j =>
      have hj : j < t.length := by simpa using hi
      show a :: t.take (j + 1) = a :: (t.take j ++ [t.getD j default])
      rw [ih j hj]

theorem buQT_vsz_ofList (l : List Val) : vsz (ofList l) = l.length + 1 + (l.map vsz).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have h : ofList (a :: t) = Val.cons a (ofList t) := rfl
    rw [h, Work.Fx.vsz_cons, ih, List.length_cons, List.map_cons, List.sum_cons]
    ring

theorem buQT_vsz_zl (l : List ℤ) : vsz (zl l) = l.length + 1 + (l.map isz).sum := by
  unfold zl
  rw [buQT_vsz_ofList, List.length_map]
  have h1 : ((l.map Val.int).map vsz) = l.map isz := by
    rw [List.map_map]
    exact List.map_congr_left (fun z _ => Work.Fx.vsz_int z)
  rw [h1]

theorem buQT_sum_le_length_mul {l : List ℕ} {M : ℕ} (h : ∀ x ∈ l, x ≤ M) :
    l.sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : a ≤ M := h a (by simp)
    have ht : ∀ x ∈ t, x ≤ M := fun x hx => h x (by simp [hx])
    have := ih ht
    rw [List.sum_cons, List.length_cons]
    nlinarith

theorem buQT_vsz_cvecVal {u : List (ℤ × ℤ)} {M : ℕ}
    (h : ∀ z ∈ u, isz z.1 ≤ M ∧ isz z.2 ≤ M) :
    vsz (cvecVal u) ≤ 3 * u.length * (M + 1) + 1 := by
  have hsum : ∀ l : List (ℤ × ℤ), (∀ z ∈ l, isz z.1 ≤ M ∧ isz z.2 ≤ M) →
      (l.map (fun z => isz z.1 + isz z.2 + 1)).sum ≤ l.length * (2 * M + 1) := by
    intro l hl
    induction l with
    | nil => simp
    | cons a t ih =>
      have ha := hl a (by simp)
      have ht : ∀ z ∈ t, isz z.1 ≤ M ∧ isz z.2 ≤ M := fun z hz => hl z (by simp [hz])
      have h1 : isz a.1 + isz a.2 + 1 ≤ 2 * M + 1 := by omega
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith [ih ht]
  unfold cvecVal
  rw [buQT_vsz_ofList, List.length_map]
  have hmap : ((u.map cfxVal).map vsz) = u.map (fun z => isz z.1 + isz z.2 + 1) := by
    rw [List.map_map]
    exact List.map_congr_left (fun z _ => Work.Fx.vsz_cfxVal z)
  rw [hmap]
  have := hsum u h
  nlinarith [Nat.zero_le u.length, Nat.zero_le M]

theorem buQT_ofList_inj : Function.Injective (ofList : List Val → Val) := by
  intro l
  induction l with
  | nil =>
    intro m h
    cases m with
    | nil => rfl
    | cons y ys => exact absurd h (by simp [ofList])
  | cons x xs ih =>
    intro m h
    cases m with
    | nil => exact absurd h.symm (by simp [ofList])
    | cons y ys =>
      have h' : Val.cons x (ofList xs) = Val.cons y (ofList ys) := h
      obtain ⟨h1, h2⟩ := Val.cons.inj h'
      rw [h1, ih h2]

theorem buQT_cfxVal_inj {a b : ℤ × ℤ} (h : cfxVal a = cfxVal b) : a = b := by
  have h1 := Val.cons.inj h
  exact Prod.ext (Val.int.inj h1.1) (Val.int.inj h1.2)

theorem buQT_map_cfxVal_inj : Function.Injective (fun u : List (ℤ × ℤ) => u.map cfxVal) := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons y ys => simp at h
  | cons x xs ih =>
    intro b h
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [buQT_cfxVal_inj h1, ih h2]

theorem buQT_cvecVal_inj {a b : List (ℤ × ℤ)} (h : cvecVal a = cvecVal b) : a = b := by
  unfold cvecVal at h
  exact buQT_map_cfxVal_inj (buQT_ofList_inj h)

theorem buQT_buInV_mono {B B' : ℕ} (h : B ≤ B') {v : List (ℤ × ℤ)} (hv : buInV B v) : buInV B' v :=
  fun z hz => buIn_mono h (hv z hz)

theorem buQT_two_p_add_le (k : ℕ) : 2 * (100 + k) + 8 ≤ 2 ^ (99 + k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h2 : 2 ^ (99 + (k + 1)) = 2 * 2 ^ (99 + k) := by
      rw [show 99 + (k + 1) = 99 + k + 1 by ring, pow_succ]; ring
    rw [h2]
    have : 2 * (100 + (k + 1)) + 8 ≤ 2 * (2 * (100 + k) + 8) := by ring_nf; omega
    linarith

theorem buQT_two_p_add_eight_le (p : ℕ) (hp : 100 ≤ p) : 2 * p + 8 ≤ 2 ^ (p - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 100 + k := ⟨p - 100, by omega⟩
  have h := buQT_two_p_add_le k
  rwa [show 99 + k = 100 + k - 1 by omega] at h

theorem buQT_quad_le (k : ℕ) :
    68 * (100 + k) * (100 + k) + 300 * (100 + k) + 300 ≤ 2 ^ (100 + k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h2 : 2 ^ (100 + (k + 1)) = 2 * 2 ^ (100 + k) := by
      rw [show 100 + (k + 1) = 100 + k + 1 by ring, pow_succ]; ring
    rw [h2]
    have h3 : 68 * (100 + (k + 1)) * (100 + (k + 1)) + 300 * (100 + (k + 1)) + 300 ≤
        2 * (68 * (100 + k) * (100 + k) + 300 * (100 + k) + 300) := by
      nlinarith
    linarith

theorem buQT_quad_le' (p : ℕ) (hp : 100 ≤ p) : 68 * p * p + 300 * p + 300 ≤ 2 ^ p := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 100 + k := ⟨p - 100, by omega⟩
  exact buQT_quad_le k

theorem buQT_egM_le (p α : ℕ) : egM p α ≤ p + 1 := by
  have h1 : Nat.sqrt p / (2 * α) ≤ Nat.sqrt p := Nat.div_le_self _ _
  have h2 : Nat.sqrt p ≤ p := Nat.sqrt_le_self p
  simp only [egM]
  omega

theorem buQT_eight_egM_le (p α : ℕ) (hp : 100 ≤ p) : 8 * egM p α ≤ 2 ^ (p - 1) := by
  have h1 : egM p α ≤ Nat.sqrt p + 1 := by
    have h : Nat.sqrt p / (2 * α) ≤ Nat.sqrt p := Nat.div_le_self _ _
    simp only [egM]
    omega
  have h2 : Nat.sqrt p ≤ p := Nat.sqrt_le_self p
  have h3 := buQT_two_p_add_eight_le p hp
  have hsq : Nat.sqrt p * Nat.sqrt p ≤ p := by
    have := Nat.sqrt_le' p
    rwa [Nat.pow_two] at this
  have hs4 : 4 ≤ Nat.sqrt p := Nat.le_sqrt.mpr (by omega)
  have h4 : 8 * Nat.sqrt p ≤ 2 * p := by nlinarith
  nlinarith [Nat.zero_le (egM p α), Nat.zero_le (Nat.sqrt p)]

theorem buQT_buWt_abs_le (p α s t : ℕ) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hrow : ∀ ℓ : ℤ, ∑ h ∈ egHset (egM p α),
      |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ))
    (ℓ : ℤ) (h : ℤ) (hh : h ∈ egHset (egM p α)) :
    |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p := by
  have h1 : |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ) :=
    le_trans (Finset.single_le_sum (f := fun h : ℤ => |(buWt p α s t ℓ h : ℝ)|)
      (fun i _ => abs_nonneg _) hh) (hrow ℓ)
  have hm : 8 * (egM p α : ℝ) ≤ (2 : ℝ) ^ (p - 1) := by
    have h := buQT_eight_egM_le p α hp
    exact_mod_cast h
  have h2p : ((2 : ℝ) ^ p) / 2 = (2 : ℝ) ^ (p - 1) := by
    have hp1 : 1 ≤ p := by omega
    conv_lhs => rw [← Nat.sub_add_cancel hp1]
    rw [pow_succ]
    ring
  linarith

theorem buQT_buWt_isz_le (p α s t : ℕ) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hrow : ∀ ℓ : ℤ, ∑ h ∈ egHset (egM p α),
      |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ))
    (ℓ h : ℤ) (hh : h ∈ egHset (egM p α)) :
    isz (buWt p α s t ℓ h) ≤ p + 3 := by
  have h1 := buQT_buWt_abs_le p α s t hα hp hrow ℓ h hh
  have h2 : (buWt p α s t ℓ h).natAbs ≤ 2 ^ p := by
    have h3 := abs_le.mp h1
    have h4 : -((2 : ℤ) ^ p) ≤ buWt p α s t ℓ h ∧ buWt p α s t ℓ h ≤ (2 : ℤ) ^ p := by
      constructor
      · exact_mod_cast h3.1
      · exact_mod_cast h3.2
    have h5 : ((buWt p α s t ℓ h).natAbs : ℤ) ≤ (2 : ℤ) ^ p := by
      rcases le_total 0 (buWt p α s t ℓ h) with hz0 | hz0
      · have he : ((buWt p α s t ℓ h).natAbs : ℤ) = buWt p α s t ℓ h := by
          rw [Int.natAbs_of_nonneg hz0]
        rw [he]; exact h4.2
      · have h8 : 0 ≤ -(buWt p α s t ℓ h) := by omega
        have he : ((buWt p α s t ℓ h).natAbs : ℤ) = -(buWt p α s t ℓ h) := by
          rw [← Int.natAbs_neg]
          exact Int.natAbs_of_nonneg h8
        rw [he]; linarith [h4.1]
    exact_mod_cast h5
  have h6 : (buWt p α s t ℓ h).natAbs < 2 ^ (p + 1) := by
    have := Nat.lt_two_pow_self (n := p)
    omega
  exact Work.Fx.isz_le_of_natAbs_lt h6

/-! ## `Pipe` adapters for `unconsV`/`consV`/`roll` -/

theorem Pipe.unconsVA {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest) (fun _ => K))
    {a b : Val} {T : List Val} : Pipe main prog (.cons a b :: T) (a :: b :: T) K := by
  intro rest vs hvs s R hR
  have hv2 : vs = .cons a b :: (T ++ rest) := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', r', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs ⟨a, b, T ++ rest, hv2⟩ s R hR
  obtain ⟨h1, h2, h3⟩ := Work.Fx.val_cons_inj3 (hvs'.symm.trans hv2)
  exact ⟨out, s', n, by rw [hout, h1, h2, h3]; rfl, hev, hn, hstk, hoth⟩

theorem Pipe.consVA {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => K))
    {a b : Val} {T : List Val} : Pipe main prog (a :: b :: T) (.cons a b :: T) K := by
  intro rest vs hvs s R hR
  have hv2 : vs = a :: b :: (T ++ rest) := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', r', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv2]; simp) s R hR
  obtain ⟨h1, h2, h3⟩ := Work.Fx.cons_inj3 (hvs'.symm.trans hv2)
  exact ⟨out, s', n, by rw [hout, h1, h2, h3]; rfl, hev, hn, hstk, hoth⟩

theorem Pipe.rollA {prog : ℕ → Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List Val} {j : ℕ} (hj : j < A.length) {B : List Val}
    (hB : A.getD j .nil :: A.eraseIdx j = B) :
    Pipe main (prog j) A B (K * (j + 1) * (Work.Fx.szl (A.take (j + 1)) + 1)) := by
  rw [← hB]
  exact Pipe.roll main h hj

/-! ## program-side helpers -/

/-- the size of a product of two bounded integers -/
theorem buQW_isz_mul_le {a b : ℤ} {m n : ℕ} (ha : a.natAbs < 2 ^ m) (hb : b.natAbs < 2 ^ n) :
    isz (a * b) ≤ m + n + 2 := by
  have h : (a * b).natAbs < 2 ^ (m + n) := by
    rw [Int.natAbs_mul, pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt ha hb
  have := Work.Fx.isz_le_of_natAbs_lt h
  omega

/-- `isz z ≤ k + 2` gives `z.natAbs < 2^k` -/
theorem buQW_natAbs_lt_of_isz_le {z : ℤ} {k : ℕ} (h : isz z ≤ k + 2) : z.natAbs < 2 ^ k := by
  have h1 : z.natAbs.size ≤ k := by simp only [isz] at h; omega
  exact Nat.size_le.mp h1

/-- a cost of the shape `KS * a` with `a ≤ 1000 (p+1)` fits in the final budget -/
theorem buQW_small_le {KS KC p a : ℕ} {Cm : ℕ → ℕ} (hKC : 1000 * KS ≤ KC)
    (ha : a ≤ 1000 * (p + 1)) :
    KS * a ≤ KC * (Cm (KC * p) + p + 1) := by
  have h1 : KC * (p + 1) ≤ KC * (Cm (KC * p) + p + 1) := Nat.mul_le_mul_left _ (by omega)
  have h2 : KS * a ≤ KS * (1000 * (p + 1)) := Nat.mul_le_mul_left _ ha
  have h3 : KS * (1000 * (p + 1)) = (1000 * KS) * (p + 1) := by ring
  rw [h3] at h2
  have h4 : (1000 * KS) * (p + 1) ≤ KC * (p + 1) := Nat.mul_le_mul_right _ hKC
  linarith

/-- the cost of a window operation -/
theorem buQW_op_le {K KS p MW : ℕ} (hK : K ≤ KS) (hMW : MW ≤ 10 * p + 60) (k : ℕ)
    (hk : k + 1 ≤ 5) : K * (k + 1) * (MW + 1) ≤ KS * (1000 * (p + 1)) := by
  have h1 : (k + 1) * (MW + 1) ≤ 5 * (10 * p + 61) := Nat.mul_le_mul hk (by omega)
  calc K * (k + 1) * (MW + 1) = K * ((k + 1) * (MW + 1)) := by ring
    _ ≤ K * (5 * (10 * p + 61)) := Nat.mul_le_mul_left _ h1
    _ ≤ KS * (5 * (10 * p + 61)) := Nat.mul_le_mul_right _ hK
    _ ≤ KS * (1000 * (p + 1)) := Nat.mul_le_mul_left _ (by omega)

/-- the cost of a `mulWord` call fits in the budget -/
theorem buQW_mul_le {kmul KC p : ℕ} {Cm : ℕ → ℕ} (hmono : Monotone Cm) (hkm : 8 * kmul ≤ KC)
    (h2 : kmul * (p + 3) ≤ KC * p) :
    kmul * (Cm (kmul * (p + 3)) + (p + 3) + 1) ≤ KC * (Cm (KC * p) + p + 1) := by
  have hc1 : Cm (kmul * (p + 3)) ≤ Cm (KC * p) := hmono h2
  have h1 : kmul * (p + 4) ≤ KC * (p + 1) := by
    have hA : kmul * (p + 4) ≤ kmul * (4 * (p + 1)) := Nat.mul_le_mul_left _ (by omega)
    have hB : kmul * (4 * (p + 1)) = (4 * kmul) * (p + 1) := by ring
    rw [hB] at hA
    exact le_trans hA (Nat.mul_le_mul_right _ (by omega))
  have h2' : kmul * Cm (kmul * (p + 3)) ≤ KC * Cm (KC * p) :=
    Nat.mul_le_mul (by omega) hc1
  calc kmul * (Cm (kmul * (p + 3)) + (p + 3) + 1)
      = kmul * Cm (kmul * (p + 3)) + kmul * (p + 4) := by ring
    _ ≤ KC * Cm (KC * p) + KC * (p + 1) := add_le_add h2' h1
    _ = KC * (Cm (KC * p) + p + 1) := by ring

/-- the cost of a whole chain of window operations -/
theorem buQW_chain_le {KS kmul KC p : ℕ} {Cm : ℕ → ℕ} (hmono : Monotone Cm)
    (hKC : 11000 * KS + 8 * kmul ≤ KC) (hkm : kmul * (p + 3) ≤ KC * p) :
    11000 * KS * (p + 1) + 2 * (kmul * (Cm (kmul * (p + 3)) + (p + 3) + 1)) ≤
      KC * (Cm (KC * p) + p + 1) := by
  have hc1 : Cm (kmul * (p + 3)) ≤ Cm (KC * p) := hmono hkm
  have h1 : 11000 * KS * (p + 1) + 2 * (kmul * (p + 4)) ≤ KC * (p + 1) := by
    have h2 : 11000 * KS ≤ KC := by omega
    have h3 : 8 * kmul ≤ KC := by omega
    nlinarith [Nat.zero_le p]
  have h4 : 2 * (kmul * Cm (kmul * (p + 3))) ≤ KC * Cm (KC * p) := by
    have h5 : 2 * kmul ≤ KC := by omega
    nlinarith [Nat.zero_le (Cm (kmul * (p + 3))), Nat.zero_le (Cm (KC * p))]
  have h6 : 2 * (kmul * (Cm (kmul * (p + 3)) + (p + 3) + 1))
      = 2 * (kmul * Cm (kmul * (p + 3))) + 2 * (kmul * (p + 4)) := by ring
  rw [h6]
  linarith

/-- a two-argument integer word as a `Pipe` -/
theorem buPipe_int2 {main prog : Cmd} {a b f : ℤ} {c : ℕ}
    (h : WordR main prog (fun vs => ∃ rest, vs = .int a :: .int b :: rest)
      (fun vs out => ∃ rest, vs = .int a :: .int b :: rest ∧ out = .int f :: rest)
      (fun _ => c)) : Pipe main prog [.int a, .int b] [.int f] c := by
  intro rest vs hvs s R hR
  have hv2 : vs = .int a :: .int b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨r', hvs', hout⟩, hev, hn, hstk, hoth⟩ := h vs ⟨rest, hv2⟩ s R hR
  obtain ⟨h1, h2, h3⟩ := Work.Fx.int_cons_inj3 (hvs'.symm.trans hv2)
  refine ⟨out, s', n, ?_, hev, hn, hstk, hoth⟩
  show out = .int f :: rest
  rw [hout, h3]

/-- a one-value word on `cfxVal` inputs as a `Pipe` -/
theorem buPipe_cfxVal {main prog : Cmd} {a f : ℤ × ℤ} {c : ℕ}
    (h : WordR main prog (fun vs => ∃ rest, vs = cfxVal a :: rest)
      (fun vs out => ∃ rest, vs = cfxVal a :: rest ∧ out = cfxVal f :: rest)
      (fun _ => c)) : Pipe main prog [cfxVal a] [cfxVal f] c := by
  intro rest vs hvs s R hR
  have hv2 : vs = cfxVal a :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨r', hvs', hout⟩, hev, hn, hstk, hoth⟩ := h vs ⟨rest, hv2⟩ s R hR
  obtain ⟨h1, h2⟩ := List.cons.inj (hvs'.symm.trans hv2)
  have h1' : cfxVal a = cfxVal a := h1
  refine ⟨out, s', n, ?_, hev, hn, hstk, hoth⟩
  show out = cfxVal f :: rest
  rw [hout, h2]

/-- a two-value word on `cfxVal` inputs as a `Pipe` -/
theorem buPipe_cfxVal2 {main prog : Cmd} {a b f : ℤ × ℤ} {c : ℕ}
    (h : WordR main prog (fun vs => ∃ rest, vs = cfxVal a :: cfxVal b :: rest)
      (fun vs out => ∃ rest, vs = cfxVal a :: cfxVal b :: rest ∧ out = cfxVal f :: rest)
      (fun _ => c)) : Pipe main prog [cfxVal a, cfxVal b] [cfxVal f] c := by
  intro rest vs hvs s R hR
  have hv2 : vs = cfxVal a :: cfxVal b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨r', hvs', hout⟩, hev, hn, hstk, hoth⟩ := h vs ⟨rest, hv2⟩ s R hR
  obtain ⟨h1, h2, h3⟩ := Work.Fx.cons_inj3 (hvs'.symm.trans hv2)
  have h1' : cfxVal a = cfxVal a := h1
  have h2' : cfxVal b = cfxVal b := h2
  refine ⟨out, s', n, ?_, hev, hn, hstk, hoth⟩
  show out = cfxVal f :: rest
  rw [hout, h3]

/-- `isz` of a Gaussian integer of norm `≤ 2^k` -/
theorem buQW_isz_le_of_gz_le_pow {k : ℕ} {z : ℤ × ℤ} (h : ‖gz z‖ ≤ (2 : ℝ) ^ k) :
    isz z.1 ≤ k + 3 ∧ isz z.2 ≤ k + 3 := by
  have hre : (gz z).re = (z.1 : ℝ) := by simp [gz]
  have him : (gz z).im = (z.2 : ℝ) := by simp [gz]
  have h1 : |(z.1 : ℝ)| ≤ (2 : ℝ) ^ k := by
    have h' := Complex.abs_re_le_norm (gz z)
    rw [hre] at h'
    exact le_trans h' h
  have h2 : |(z.2 : ℝ)| ≤ (2 : ℝ) ^ k := by
    have h' := Complex.abs_im_le_norm (gz z)
    rw [him] at h'
    exact le_trans h' h
  constructor
  · have e : z.1.natAbs ≤ 2 ^ k := by
      have h3 := abs_le.mp h1
      have h4 : (z.1 : ℝ) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 := by
        nlinarith [h3.1, h3.2, sq_nonneg (z.1 : ℝ), sq_nonneg ((2 : ℝ) ^ k - (z.1 : ℝ)),
          (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)]
      have h5 : z.1 ^ 2 ≤ (((2 ^ k : ℕ)) : ℤ) ^ 2 := by
        have h6 : (((z.1 ^ 2 : ℤ)) : ℝ) ≤ (((((2 ^ k : ℕ)) : ℤ) ^ 2 : ℤ) : ℝ) := by
          push_cast; push_cast at h4; exact h4
        exact_mod_cast h6
      have h7 := (Int.natAbs_le_iff_sq_le (a := z.1) (b := ((2 ^ k : ℕ) : ℤ))).mpr h5
      simpa using h7
    have hlt : z.1.natAbs < 2 ^ (k + 1) :=
      lt_of_le_of_lt e (Nat.pow_lt_pow_right (by norm_num) (by omega))
    exact le_trans (Work.Fx.isz_le_of_natAbs_lt hlt) (by omega)
  · have e : z.2.natAbs ≤ 2 ^ k := by
      have h3 := abs_le.mp h2
      have h4 : (z.2 : ℝ) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 := by
        nlinarith [h3.1, h3.2, sq_nonneg (z.2 : ℝ), sq_nonneg ((2 : ℝ) ^ k - (z.2 : ℝ)),
          (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)]
      have h5 : z.2 ^ 2 ≤ (((2 ^ k : ℕ)) : ℤ) ^ 2 := by
        have h6 : (((z.2 ^ 2 : ℤ)) : ℝ) ≤ (((((2 ^ k : ℕ)) : ℤ) ^ 2 : ℤ) : ℝ) := by
          push_cast; push_cast at h4; exact h4
        exact_mod_cast h6
      have h7 := (Int.natAbs_le_iff_sq_le (a := z.2) (b := ((2 ^ k : ℕ) : ℤ))).mpr h5
      simpa using h7
    have hlt : z.2.natAbs < 2 ^ (k + 1) :=
      lt_of_le_of_lt e (Nat.pow_lt_pow_right (by norm_num) (by omega))
    exact le_trans (Work.Fx.isz_le_of_natAbs_lt hlt) (by omega)

/-- `buInV B v` with `B ≤ 2^(p+2)` bounds the `isz` of the coordinates by `p + 5`. -/
theorem buQW_isz_of_buInV {B p : ℕ} (hB : B ≤ 2 ^ (p + 2)) {v : List (ℤ × ℤ)}
    (hv : buInV B v) : ∀ z ∈ v, isz z.1 ≤ p + 5 ∧ isz z.2 ≤ p + 5 := by
  intro z hz
  have h1 : ‖gz z‖ ≤ (2 : ℝ) ^ (p + 2) := by
    have h := (buInV_iff B v).mp hv z hz
    have h2 : (B : ℝ) ≤ ((2 : ℕ) ^ (p + 2) : ℝ) := by exact_mod_cast hB
    have h3 : ((2 : ℕ) ^ (p + 2) : ℝ) = (2 : ℝ) ^ (p + 2) := by push_cast; ring
    linarith
  exact buQW_isz_le_of_gz_le_pow h1

/-- `buRowS` is monotone in the number of columns. -/
theorem buRowS_mono (Wt : ℤ → ℤ → ℤ) (m : ℕ) (ℓ : ℤ) : ∀ i j : ℕ, i ≤ j →
    buRowS Wt m ℓ i ≤ buRowS Wt m ℓ j := by
  intro i j hij
  have htake : (egHs m).take i = ((egHs m).take j).take i := by
    rw [List.take_take, min_eq_left hij]
  have h1 : ((egHs m).take i).map (fun h => |(Wt ℓ h : ℝ)|)
      = (((egHs m).take j).map (fun h => |(Wt ℓ h : ℝ)|)).take i := by
    rw [htake, List.map_take]
  rw [buRowS, buRowS, h1]
  set l := ((egHs m).take j).map (fun h => |(Wt ℓ h : ℝ)|) with hl
  have h2 : l.sum = (l.take i).sum + (l.drop i).sum := by
    rw [← List.sum_append, List.take_append_drop]
  rw [h2]
  have h3 : 0 ≤ (l.drop i).sum :=
    List.sum_nonneg (fun x hx => by
      rcases List.mem_map.mp (List.mem_of_mem_drop hx) with ⟨h, _, rfl⟩
      exact abs_nonneg _)
  linarith

/-- The partial row sum is bounded by the full row sum. -/
theorem buRowS_le_row (Wt : ℤ → ℤ → ℤ) (m : ℕ) (ℓ : ℤ) (i : ℕ) (hi : i ≤ 2 * m) :
    buRowS Wt m ℓ i ≤ ∑ h ∈ egHset m, |(Wt ℓ h : ℝ)| := by
  rw [← buRowS_full Wt m ℓ]
  exact buRowS_mono Wt m ℓ i (2 * m) hi

/-- The entries of the partial fold have `isz ≤ 2p + 8`. -/
theorem buQW_fold_isz (p α s t : ℕ) (hp : 100 ≤ p)
    (hrow : ∀ ℓ : ℤ, ∑ h ∈ egHset (egM p α),
      |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ))
    (B : ℕ) (hB : B ≤ 2 ^ (p + 2)) (v : List (ℤ × ℤ)) (hv : v.length = s)
    (hbv : buInV B v) (i : ℕ) (hi : i ≤ 2 * egM p α) (ℓ : ℕ) (hℓ : ℓ < s) :
    isz ((buPFold (buWt p α s t) s (egM p α) v i).getD ℓ (0, 0)).1 ≤ 2 * p + 8 ∧
    isz ((buPFold (buWt p α s t) s (egM p α) v i).getD ℓ (0, 0)).2 ≤ 2 * p + 8 := by
  have hBnn : (0 : ℝ) ≤ (B : ℝ) := by positivity
  have hgz := buPFold_gz_le (buWt p α s t) s (egM p α) B v hv
    (fun z hz => (buInV_iff B v).mp hbv z hz) i (by simpa [buColsN_length] using hi) ℓ hℓ
  have hrow' : buRowS (buWt p α s t) (egM p α) (ℓ : ℤ) (2 * egM p α)
      ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ) := by
    rw [buRowS_full]; exact hrow (ℓ : ℤ)
  have hmono := buRowS_mono (buWt p α s t) (egM p α) (ℓ : ℤ) i (2 * egM p α) hi
  have h8 : 8 * (egM p α : ℝ) ≤ (2 : ℝ) ^ (p - 1) := by
    have h := buQT_eight_egM_le p α hp
    exact_mod_cast h
  have h2p : (2 : ℝ) ^ p / 2 = (2 : ℝ) ^ (p - 1) := by
    have hp1 : 1 ≤ p := by omega
    have hthis : (2 : ℝ) ^ p = (2 : ℝ) ^ (p - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hp1]
    rw [hthis]; ring
  have hbs : buRowS (buWt p α s t) (egM p α) (ℓ : ℤ) i ≤ (2 : ℝ) ^ p := by
    have h1 : buRowS (buWt p α s t) (egM p α) (ℓ : ℤ) i
        ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ) := le_trans hmono hrow'
    rw [h2p] at h1
    linarith
  have hBB : (B : ℝ) ≤ (2 : ℝ) ^ (p + 2) := by
    have h := hB
    have h2 : ((2 : ℕ) ^ (p + 2) : ℝ) = (2 : ℝ) ^ (p + 2) := by push_cast; ring
    calc (B : ℝ) ≤ ((2 : ℕ) ^ (p + 2) : ℝ) := by exact_mod_cast h
      _ = (2 : ℝ) ^ (p + 2) := h2
  have hunt : ‖gz ((buPFold (buWt p α s t) s (egM p α) v i).getD ℓ (0, 0))‖
      ≤ (2 : ℝ) ^ (2 * p + 2) := by
    refine le_trans hgz ?_
    calc buRowS (buWt p α s t) (egM p α) (ℓ : ℤ) i * (B : ℝ)
        ≤ (2 : ℝ) ^ p * (2 : ℝ) ^ (p + 2) := mul_le_mul hbs hBB hBnn (by positivity)
      _ = (2 : ℝ) ^ (2 * p + 2) := by rw [← pow_add]; ring_nf
  have hfin := buQW_isz_le_of_gz_le_pow (k := 2 * p + 2) hunt
  exact ⟨le_trans hfin.1 (by omega), le_trans hfin.2 (by omega)⟩

/-- The `vsz` of a column record of the table. -/
theorem buQW_col_vsz_le (p α s t : ℕ) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hrow : ∀ ℓ : ℤ, ∑ h ∈ egHset (egM p α),
      |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ))
    {h : ℤ} (hh : h ∈ egHs (egM p α)) :
    vsz (Val.cons (.int h) (buCol p α s t h)) ≤ 100 * (s + 1) * (p + 1) := by
  have hmem : h ∈ egHset (egM p α) := by
    rw [← (buQWhs (egM p α)).1, List.mem_toFinset]; exact hh
  have hiszh : isz h ≤ p + 3 := by
    have h2 : h.natAbs ≤ egM p α := (buQWhs (egM p α)).2.2.2.2.1 h hh
    have h3 : h.natAbs ≤ p + 1 := le_trans h2 (buQT_egM_le p α)
    have h4 : h.natAbs < 2 ^ (p + 1) :=
      lt_of_le_of_lt h3 (Nat.lt_two_pow_self (n := p + 1))
    exact Work.Fx.isz_le_of_natAbs_lt h4
  have hcol : vsz (buCol p α s t h) ≤ (s + 1) * (p + 4) := by
    have h1 : vsz (buCol p α s t h) =
        s + 1 + ((List.ofFn (fun ℓ : Fin s => buWt p α s t (ℓ : ℤ) h)).map isz).sum := by
      unfold buCol
      rw [buQT_vsz_zl]
      simp
    rw [h1]
    have h2 : ((List.ofFn (fun ℓ : Fin s => buWt p α s t (ℓ : ℤ) h)).map isz).sum ≤ s * (p + 3) := by
      have hb := buQT_sum_le_length_mul
        (l := (List.ofFn (fun ℓ : Fin s => buWt p α s t (ℓ : ℤ) h)).map isz) (M := p + 3) ?_
      simpa using hb
      intro x hx
      rcases List.mem_map.mp hx with ⟨z, hz, rfl⟩
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hz
      rw [← hi]
      exact buQT_buWt_isz_le p α s t hα hp hrow _ h hmem
    nlinarith [Nat.zero_le s, Nat.zero_le p]
  rw [Work.Fx.vsz_cons, Work.Fx.vsz_int]
  nlinarith [Nat.zero_le s, Nat.zero_le p]

/-- the size of the whole column table -/
theorem buQW_colsT_vsz_le (p α s t : ℕ) (hs : 2 ≤ s) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hrow : ∀ ℓ : ℤ, ∑ h ∈ egHset (egM p α),
      |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ)) :
    vsz (buColsT p α s t) ≤ 1000 * (egM p α + 1) * (s + 1) * (p + 1) := by
  have hm : egM p α ≤ p + 1 := buQT_egM_le p α
  have hlen : ((egHs (egM p α)).map (fun h => Val.cons (.int h) (buCol p α s t h))).length
      = 2 * egM p α := by
    rw [List.length_map, buQWhs_length]
  have hsum : ((List.map (fun h => Val.cons (.int h) (buCol p α s t h))
      (egHs (egM p α))).map vsz).sum ≤ (2 * egM p α) * (100 * (s + 1) * (p + 1)) := by
    have hb := buQT_sum_le_length_mul
      (l := (List.map (fun h => Val.cons (.int h) (buCol p α s t h)) (egHs (egM p α))).map vsz)
      (M := 100 * (s + 1) * (p + 1)) ?_
    rw [List.length_map, hlen] at hb
    exact hb
    intro x hx
    rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
    rcases List.mem_map.mp ha with ⟨h, hh, rfl⟩
    exact buQW_col_vsz_le p α s t hα hp hrow hh
  unfold buColsT
  rw [buQT_vsz_ofList, hlen]
  have hm1 : 1 ≤ egM p α := by
    show 1 ≤ Nat.sqrt p / (2 * α) + 1
    exact le_add_of_nonneg_left (Nat.zero_le _)
  have hQ1 : 1 ≤ (s + 1) * (p + 1) := by
    have h := Nat.mul_le_mul (show 1 ≤ s + 1 by omega) (show 1 ≤ p + 1 by omega)
    simpa using h
  have hmQ : egM p α ≤ egM p α * ((s + 1) * (p + 1)) := by
    have h := Nat.mul_le_mul_left (egM p α) hQ1
    rwa [Nat.mul_one] at h
  have h1 : 2 * egM p α + 1 + (2 * egM p α) * (100 * (s + 1) * (p + 1))
      ≤ 1000 * (egM p α + 1) * (s + 1) * (p + 1) := by
    nlinarith [hm1, hmQ, hQ1, Nat.zero_le (egM p α), Nat.zero_le s, Nat.zero_le p]
  have h2 : 2 * egM p α + 1 + (List.map vsz (List.map (fun h => Val.cons (.int h) (buCol p α s t h))
      (egHs (egM p α)))).sum ≤ 2 * egM p α + 1 + (2 * egM p α) * (100 * (s + 1) * (p + 1)) := by
    have := hsum
    omega
  exact le_trans h2 h1

/-- a bound on the size of the first `k+1` values of an explicit window -/
theorem buQW_szl_le_of {A : List Val} (MV : ℕ) {k : ℕ} (h : ∀ v ∈ A, vsz v ≤ MV) :
    Work.Fx.szl (A.take (k + 1)) ≤ (k + 1) * MV := by
  refine le_trans (szl_le_len_mul (fun v hv => h v (List.mem_of_mem_take hv))) ?_
  rw [List.length_take]
  exact Nat.mul_le_mul_right _ (min_le_left _ _)

/-- the size of the first `k+1` entries of a window, bounded by `8 * SB + 1` -/
theorem buQW_szl_succ_le {A : List Val} {SB : ℕ} (h : ∀ v ∈ A, vsz v ≤ SB) {k : ℕ}
    (hk : k + 1 ≤ 8) : Work.Fx.szl (A.take (k + 1)) + 1 ≤ 8 * SB + 1 := by
  have h1 : Work.Fx.szl (A.take (k + 1)) ≤ (k + 1) * SB := buQW_szl_le_of SB h
  have h2 : (k + 1) * SB ≤ 8 * SB := Nat.mul_le_mul_right SB hk
  omega

/-- the cost of a window operation on a window of values of size `≤ SB` -/
theorem buQW_opc_le {K KS SB : ℕ} (hK : K ≤ KS) (hSB : 1 ≤ SB) {k Z : ℕ} (hk : k + 1 ≤ 8)
    (hZ : Z ≤ 8 * SB + 1) : K * (k + 1) * Z ≤ KS * 100 * SB := by
  have h1 : K * (k + 1) * Z ≤ KS * 8 * (8 * SB + 1) := Nat.mul_le_mul (Nat.mul_le_mul hK hk) hZ
  have h2 : 8 * (8 * SB + 1) ≤ 100 * SB := by omega
  have h3 : KS * (8 * (8 * SB + 1)) ≤ KS * (100 * SB) := Nat.mul_le_mul_left KS h2
  have h4 : KS * 8 * (8 * SB + 1) = KS * (8 * (8 * SB + 1)) := by ring
  have h5 : KS * (100 * SB) = KS * 100 * SB := by ring
  linarith [h1, h3]

end Work.Resample
