import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Kernel.Raw
import Submission.Work.ConvR.basic
import Submission.Work.ConvR.permTop

/-! # Auxiliaries for `Work.MainP.prop52` (paper Proposition 5.2)

Elementary facts about the sup norm on `Fin n → ℂ`, conjugation of fixed-point complex numbers,
sizes of encoded values, difference-linearity of `dftMulti`, the `KernelLib` step words used by
the §5.2 pipeline, and the uniform cost allowance bounding every elementary step of that
pipeline. -/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-! ## The sup norm on `Fin n → ℂ` -/

/-- The norm on `Fin n → ℂ` is the sup norm: an entrywise bound bounds the norm. -/
theorem pi_norm_le_of_forall {n : ℕ} {f : Fin n → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖f i‖ ≤ C) : ‖f‖ ≤ C :=
  (pi_norm_le_iff_of_nonneg hC).mpr h

/-- The norm of a single entry is at most the norm. -/
theorem norm_apply_le {n : ℕ} (f : Fin n → ℂ) (i : Fin n) : ‖f i‖ ≤ ‖f‖ :=
  norm_le_pi_norm f i

/-- `(2^p)·‖f‖ ≤ E` follows from the same bound for every entry. -/
theorem two_pow_norm_le_of_forall {n p : ℕ} {f : Fin n → ℂ} {E : ℝ} (hE : 0 ≤ E)
    (h : ∀ i, (2 : ℝ) ^ p * ‖f i‖ ≤ E) : (2 : ℝ) ^ p * ‖f‖ ≤ E := by
  have hp : (0 : ℝ) < 2 ^ p := pow_pos (by norm_num) p
  have hle : ∀ i, ‖f i‖ ≤ E / 2 ^ p := by
    intro i
    rw [le_div_iff₀ hp]
    calc ‖f i‖ * 2 ^ p = 2 ^ p * ‖f i‖ := by ring
      _ ≤ E := h i
  calc (2 : ℝ) ^ p * ‖f‖ ≤ (2 : ℝ) ^ p * (E / 2 ^ p) :=
        mul_le_mul_of_nonneg_left (pi_norm_le_of_forall (div_nonneg hE (le_of_lt hp)) hle)
          (le_of_lt hp)
    _ = E := by field_simp

/-! ## Conjugation -/

/-- `fxC` commutes with complex conjugation. -/
theorem fxC_conj (p : ℕ) (z : ℤ × ℤ) : fxC p (z.1, -z.2) = starRingEnd ℂ (fxC p z) := by
  simp only [fxC, map_div₀, map_add, map_mul, map_pow, map_ofNat, map_intCast, Complex.conj_I]
  push_cast
  ring

/-- Conjugation preserves the disc condition `C̃◦`. -/
theorem inDisc_conj' {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : inDisc p (z.1, -z.2) := by
  simp only [inDisc] at h ⊢
  nlinarith [h]

/-- The conjugate pair map on `ℤ × ℤ`. -/
def conjP (z : ℤ × ℤ) : ℤ × ℤ := (z.1, -z.2)

@[simp] theorem conjP_apply (z : ℤ × ℤ) : conjP z = (z.1, -z.2) := rfl

theorem fxC_conjP (p : ℕ) (z : ℤ × ℤ) : fxC p (conjP z) = starRingEnd ℂ (fxC p z) :=
  fxC_conj p z

/-- Reading a conjugated list at an index. -/
theorem conjP_getD (zs : List (ℤ × ℤ)) (i : ℕ) :
    (zs.map conjP).getD i (0, 0) = conjP (zs.getD i (0, 0)) := by
  induction zs generalizing i with
  | nil => cases i <;> rfl
  | cons a t ih => cases i with
    | zero => rfl
    | succ j => simpa [List.getD_cons_succ] using ih j

/-- `Approx` is preserved by conjugating the fixed-point vector. -/
theorem approx_conj {p n : ℕ} {zs : List (ℤ × ℤ)} {v : Fin n → ℂ} {e : ℝ}
    (h : Approx p zs v e) : Approx p (zs.map conjP) (fun i => starRingEnd ℂ (v i)) e := by
  obtain ⟨hlen, hdisc⟩ := h.1
  refine ⟨⟨by simp [hlen], ?_⟩, ?_⟩
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := List.mem_map.mp hz
    exact inDisc_conj' (hdisc z₀ hz₀)
  · intro i
    rw [conjP_getD, fxC_conjP, ← map_sub (starRingEnd ℂ), Complex.norm_conj]
    exact h.2 i

/-- `fxVec` of a conjugated vector is the conjugate of `fxVec`. -/
theorem fxVec_conjP (p n : ℕ) (zs : List (ℤ × ℤ)) :
    fxVec p n (zs.map conjP) = fun i => starRingEnd ℂ (fxVec p n zs i) := by
  funext i
  simp only [fxVec, conjP_getD, fxC_conjP]

/-! ## Sizes -/

theorem isz_natCast_le (n : ℕ) : isz (n : ℤ) ≤ n + 2 := by
  simp only [isz, Int.natAbs_natCast]
  have h : n.size ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · rw [Nat.size_le]
      exact Nat.lt_two_pow_self
  omega

theorem sum_vsz_le {L : List Val} {B : ℕ} (h : ∀ v ∈ L, vsz v ≤ B) :
    (L.map vsz).sum ≤ L.length * B := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have ha : vsz a ≤ B := h a (by simp)
    have ht : (t.map vsz).sum ≤ t.length * B := ih (fun v hv => h v (by simp [hv]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith [ha, ht]

/-! ## Difference-linearity of `dftMulti` -/

/-- `dftMulti` is additive on differences (linearity conjunct of `DFTMathProp`). -/
theorem dftMulti_sub (hDFT : DFTMathProp) {ts : List ℕ} (hpos : ∀ t ∈ ts, 0 < t)
    (sgn : ℤ) (u v : Fin ts.prod → ℂ) :
    dftMulti ts sgn (u - v) = dftMulti ts sgn u - dftMulti ts sgn v := by
  have h := (hDFT ts hpos).2.1 sgn (-1) v u
  have hv : (-1 : ℂ) • v + u = u - v := by
    ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, neg_one_smul]; ring
  have hv2 : (-1 : ℂ) • dftMulti ts sgn v + dftMulti ts sgn u =
      dftMulti ts sgn u - dftMulti ts sgn v := by
    ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, neg_one_smul]; ring
  rw [hv, hv2] at h
  exact h

/-- The sup-norm contraction of the transform (Example 2.6 / `DFTMathProp`). -/
theorem dftMulti_norm_le (hDFT : DFTMathProp) {ts : List ℕ} (hpos : ∀ t ∈ ts, 0 < t)
    (sgn : ℤ) (u : Fin ts.prod → ℂ) : ‖dftMulti ts sgn u‖ ≤ ‖u‖ :=
  (hDFT ts hpos).1 sgn u

/-! ## Step words -/

/-- A `pick` step on an explicit window above an arbitrary tail. -/
theorem pickStep {main : Cmd} {pickP : ℕ → Cmd} {Kp : ℕ}
    (hpick : ∀ (k : ℕ), WordR main (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => Kp * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (k : ℕ) (L : List Val) (rest : List Val) (C : ℕ) (hk : k < L.length)
    (hC : Kp * (k + 1) * (((L.take (k + 1)).map vsz).sum + 1) ≤ C) :
    Work.ConvR.WordC main (pickP k) (fun vs => vs = L ++ rest)
      (fun _ out => out = L.getD k .nil :: L ++ rest) C := by
  intro vs hvs s R hR
  have hlen : k < vs.length := by
    rw [hvs, List.length_append]; exact lt_of_lt_of_le hk (Nat.le_add_right _ _)
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ := hpick k vs hlen s R hR
  refine ⟨out, s', n, ?_, he, ?_, ?_, hoth⟩
  · have h : out = L.getD k .nil :: L ++ rest := by
      rw [hQ, hvs, Work.ConvR.getD_append_lt hk]
      simp only [List.cons_append]
    exact h
  · have hβ : n ≤ Kp * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1) := hn
    have hcost : Kp * (k + 1) * ((((L ++ rest).take (k + 1)).map vsz).sum + 1) ≤ C := by
      rw [List.take_append_of_le_length (Nat.succ_le_of_lt hk)]; exact hC
    rw [hvs] at hβ
    exact le_trans hβ hcost
  · exact hstk

/-- A `permTop` step on an explicit window above an arbitrary tail. -/
theorem permStep {main : Cmd} {permP : List ℕ → Cmd} {Kp : ℕ}
    (hperm : ∀ (main : Cmd) (n : ℕ) (σ : List ℕ) (head tail : List Val),
      head.length = n → σ.length = n → σ.Perm (List.range n) →
      WordR main (permP σ) (fun vs => vs = head ++ tail)
        (fun _ out => out = σ.map (fun i => head.getD i .nil) ++ tail)
        (fun _ => Kp * (n + 1) * (n + 1) * (((head.map vsz).sum) + 1)))
    (n : ℕ) (σ : List ℕ) (head tail : List Val) (C : ℕ) (h1 : head.length = n)
    (h2 : σ.length = n) (h3 : σ.Perm (List.range n))
    (hC : Kp * (n + 1) * (n + 1) * (((head.map vsz).sum) + 1) ≤ C) :
    Work.ConvR.WordC main (permP σ) (fun vs => vs = head ++ tail)
      (fun _ out => out = σ.map (fun i => head.getD i .nil) ++ tail) C := by
  intro vs hvs s R hR
  obtain ⟨out, s', n', hQ, he, hn, hstk, hoth⟩ :=
    hperm main n σ head tail h1 h2 h3 vs hvs s R hR
  exact ⟨out, s', n', hQ, he, le_trans hn hC, hstk, hoth⟩


end Work.MainP
