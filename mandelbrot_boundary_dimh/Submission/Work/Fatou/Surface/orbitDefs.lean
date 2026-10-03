import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Fatou.Qreg.fatouFundamental
import Submission.Work.Fatou.Qreg.fatouInjOnQ
import Submission.Work.Fatou.Qreg.forwardIterate
import Submission.Work.Fatou.Qreg.backwardIterate

/-!
# Orbit pieces and meets in Shishikura's region `𝒬(b₁,b₂)`

This file sets up the vocabulary used by `Work.Fatou.Surface.orbitCoord`: the orbit coordinate of a
near-translation `F` on `𝒬 = Qreg b₁ b₂` split by a vertical line `Re = x₀` of `𝒬`.

* `Piece b₁ b₂ F z n` : the first `n+1` iterates `z, F z, …, F^[n] z` all lie in `𝒬`;
* `Meet b₁ b₂ F z z' a b` : the forward orbits of `z` and `z'` meet inside `𝒬` after `a` resp. `b`
  steps, `F^[a] z = F^[b] z'`;
* `Spec b₁ b₂ F x₀ z p` : `p = (s, k)` is a candidate (representative, level) pair for `z`, `s` in
  the fundamental strip and `z` on the orbit of `s` at signed distance `k`, in the normalised form
  `Meet s z 0 k` or `Meet s z k 0`.

The fundamental input is Shishikura's Prop. A.2.1(i) (`Work.Fatou.Qreg.fatouFundamental`): every
`z ∈ 𝒬` lies on the forward orbit of some point `s` of the fundamental strip
`fundStrip F 𝒬 x₀ = {z ∈ 𝒬 | x₀ ≤ Re z ∧ every 𝒬-preimage of z has Re < x₀}`.

The elementary facts proved here are the ones shared by every downstream argument: the orbit pieces
of a point can be shifted and concatenated (`Piece.of_iterate`, `Piece.trans`), the real part grows
by at least `31/32` at every step (`iter_re_mono`), `F` is injective on `𝒬`
(`Work.Fatou.Qreg.fatouInjOnQ`), hence the iterate of a point inside `𝒬` determines the point
(`iter_injOn`) as well as the number of steps (`iter_eq_of_pieces`, `iter_eq_self`).  In the
fundamental strip the real part can never come back down, which forces `N = 0` in
`fund_iterate_eq`: no point of the fundamental strip is a non-trivial forward iterate of another.
-/

namespace Work.Fatou.Surface

open Set Metric Complex MandelDim
open scoped Topology

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}

/-- The orbit piece condition: the first `n + 1` iterates of `z` under `F` stay in `𝒬`. -/
def Piece (b₁ b₂ : Option ℂ) (F : ℂ → ℂ) (z : ℂ) (n : ℕ) : Prop :=
  ∀ j ≤ n, F^[j] z ∈ MandelDim.Qreg b₁ b₂

/-- Two points meet on a common forward orbit inside `𝒬`: `F^[a] z = F^[b] z'`, with both pieces
inside `𝒬`. -/
def Meet (b₁ b₂ : Option ℂ) (F : ℂ → ℂ) (z z' : ℂ) (a b : ℕ) : Prop :=
  F^[a] z = F^[b] z' ∧ Piece b₁ b₂ F z a ∧ Piece b₁ b₂ F z' b

/-- A candidate (representative, level) pair for `z`: the representative `p.1` lies in the
fundamental strip, and `z` lies on the orbit of `p.1` at signed distance `p.2`, in the normalised
form `Meet p.1 z a 0` (then `p.2 = a`) or `Meet p.1 z 0 b` (then `p.2 = -b`). -/
def Spec (b₁ b₂ : Option ℂ) (F : ℂ → ℂ) (x₀ : ℝ) (z : ℂ) (p : ℂ × ℤ) : Prop :=
  p.1 ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) x₀ ∧
    ∃ a b : ℕ, Meet b₁ b₂ F p.1 z a b ∧ (a = 0 ∨ b = 0) ∧ p.2 = (a : ℤ) - (b : ℤ)

section Basic

@[simp] theorem piece_iff {z : ℂ} {n : ℕ} :
    Piece b₁ b₂ F z n ↔ ∀ j ≤ n, F^[j] z ∈ MandelDim.Qreg b₁ b₂ := Iff.rfl

theorem piece_mono {z : ℂ} {m n : ℕ} (h : Piece b₁ b₂ F z n) (hmn : m ≤ n) :
    Piece b₁ b₂ F z m :=
  fun j hj => h j (le_trans hj hmn)

theorem piece_zero {z : ℂ} (hz : z ∈ MandelDim.Qreg b₁ b₂) : Piece b₁ b₂ F z 0 := by
  intro j hj
  rw [Nat.le_zero.mp hj]
  simpa only [Function.iterate_zero_apply] using hz

theorem piece_at {z : ℂ} {n : ℕ} (h : Piece b₁ b₂ F z n) : F^[n] z ∈ MandelDim.Qreg b₁ b₂ :=
  h n le_rfl

/-- Shifting an orbit piece: the piece of length `a + n` starting at `z` gives a piece of length `n`
starting at `F^[a] z`. -/
theorem piece_of_iterate {z : ℂ} {a n : ℕ} (h : Piece b₁ b₂ F z (a + n)) :
    Piece b₁ b₂ F (F^[a] z) n := by
  intro j hj
  rw [← Function.iterate_add_apply]
  exact h (j + a) (by omega)

/-- Concatenating orbit pieces. -/
theorem piece_trans {z : ℂ} {a n : ℕ} (h₁ : Piece b₁ b₂ F z a)
    (h₂ : Piece b₁ b₂ F (F^[a] z) n) : Piece b₁ b₂ F z (a + n) := by
  intro j hj
  by_cases hja : j ≤ a
  · exact h₁ j hja
  · have hle : a ≤ j := le_of_lt (lt_of_not_ge hja)
    have hsplit : F^[j] z = F^[j - a] (F^[a] z) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
    rw [hsplit]
    exact h₂ (j - a) (by omega)

theorem meet_symm {z z' : ℂ} {a b : ℕ} (h : Meet b₁ b₂ F z z' a b) :
    Meet b₁ b₂ F z' z b a :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

theorem meet_refl {z : ℂ} (hz : z ∈ MandelDim.Qreg b₁ b₂) : Meet b₁ b₂ F z z 0 0 :=
  ⟨rfl, piece_zero hz, piece_zero hz⟩

end Basic

section Mechanics

/-- One step of `F` increases the real part by at least `31/32`. -/
theorem re_step {z : ℂ} (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (hz : z ∈ MandelDim.Qreg b₁ b₂) : z.re + 31 / 32 ≤ (F z).re :=
  (Work.Fatou.Qreg.re_step_bounds (F := F) (u := z) (hF.2 z hz).1).1

/-- Along an orbit piece in `𝒬` the real part increases by at least `31/32` at every step. -/
theorem iter_re_mono {z : ℂ} {n : ℕ} (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (hp : Piece b₁ b₂ F z n) :
    z.re + (n : ℝ) * (31 / 32) ≤ (F^[n] z).re := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp' : Piece b₁ b₂ F z n := piece_mono hp (Nat.le_succ n)
    have hmem : F^[n] z ∈ MandelDim.Qreg b₁ b₂ := hp n (Nat.le_succ n)
    have hstep : (F^[n] z).re + 31 / 32 ≤ (F^[n.succ] z).re := by
      rw [Function.iterate_succ_apply']
      exact re_step hF hmem
    have := ih hp'
    push_cast
    linarith

/-- **Injectivity of the iterate.**  `F` is injective on `𝒬`, so the `k`-th iterate of `F` is
injective on the points whose orbit piece of length `k` stays in `𝒬`. -/
theorem iter_injOn {z z' : ℂ} {k : ℕ} (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (hz : Piece b₁ b₂ F z k) (hz' : Piece b₁ b₂ F z' k) (h : F^[k] z = F^[k] z') : z = z' := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have hinj : Set.InjOn F (MandelDim.Qreg b₁ b₂) :=
      Work.Fatou.Qreg.fatouInjOnQ b₁ b₂ F hadm hF
    have hzk : F^[k] z ∈ MandelDim.Qreg b₁ b₂ := hz k (Nat.le_succ k)
    have hz'k : F^[k] z' ∈ MandelDim.Qreg b₁ b₂ := hz' k (Nat.le_succ k)
    have hstep : F^[k] z = F^[k] z' :=
      hinj hzk hz'k (by simpa only [Function.iterate_succ_apply'] using h)
    exact ih (piece_mono hz (Nat.le_succ k)) (piece_mono hz' (Nat.le_succ k)) hstep

/-- No orbit piece in `𝒬` is closed: if `F^[k] z = z` with the piece in `𝒬` then `k = 0`. -/
theorem iter_eq_self {z : ℂ} {k : ℕ} (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (hz : z ∈ MandelDim.Qreg b₁ b₂) (hp : Piece b₁ b₂ F z k) (h : F^[k] z = z) : k = 0 := by
  have hmono := iter_re_mono (b₁ := b₁) (b₂ := b₂) hF hp
  rw [h] at hmono
  have hk : ((k : ℝ) * (31 / 32)) ≤ 0 := by linarith
  have h31 : (0 : ℝ) < 31 / 32 := by norm_num
  have hk' : (k : ℝ) ≤ 0 := by nlinarith
  have h0 : (k : ℝ) = 0 := le_antisymm hk' (Nat.cast_nonneg k)
  exact Nat.cast_eq_zero.mp h0

/-- The real part of the `N`-th iterate determines `N` as soon as the two pieces between the two
indices stay in `𝒬`. -/
theorem iter_eq_of_pieces {z : ℂ} {N M : ℕ} (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (hN : Piece b₁ b₂ F z N) (hM : Piece b₁ b₂ F z M) (h : F^[N] z = F^[M] z) : N = M := by
  rcases le_total N M with hNM | hMN
  · have hpiece : Piece b₁ b₂ F (F^[N] z) (M - N) :=
      piece_of_iterate (by rw [Nat.add_sub_cancel' hNM]; exact hM)
    have hmem : F^[N] z ∈ MandelDim.Qreg b₁ b₂ := piece_at hN
    have hfix : F^[M - N] (F^[N] z) = F^[N] z := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hNM, h]
    have h0 := iter_eq_self hF hmem hpiece hfix
    omega
  · have hpiece : Piece b₁ b₂ F (F^[M] z) (N - M) :=
      piece_of_iterate (by rw [Nat.add_sub_cancel' hMN]; exact hN)
    have hmem : F^[M] z ∈ MandelDim.Qreg b₁ b₂ := piece_at hM
    have hfix : F^[N - M] (F^[M] z) = F^[M] z := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hMN, ← h]
    have h0 := iter_eq_self hF hmem hpiece hfix
    omega

end Mechanics

section Fundamental

theorem fund_mem {s : ℂ} (hs : s ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) x₀) :
    s ∈ MandelDim.Qreg b₁ b₂ := hs.1

theorem fund_re_ge {s : ℂ} (hs : s ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) x₀) :
    x₀ ≤ s.re := hs.2.1

theorem fund_pre_re_lt {s : ℂ} (hs : s ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) x₀)
    {w : ℂ} (hw : w ∈ MandelDim.Qreg b₁ b₂) (h : F w = s) : w.re < x₀ := hs.2.2 w hw h

/-- **No point of the fundamental strip is a non-trivial forward iterate of another.**  If `s` and
`s'` both lie in the fundamental strip and `F^[N] s = s'` with the piece in `𝒬`, then `N = 0` and
`s = s'`. -/
theorem fund_iterate_eq {s s' : ℂ} {N : ℕ} (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (hs : s ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) x₀)
    (hs' : s' ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) x₀)
    (hp : Piece b₁ b₂ F s N) (h : F^[N] s = s') : N = 0 ∧ s = s' := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨rfl, by simpa using h⟩
  · exfalso
    have hmem : F^[N - 1] s ∈ MandelDim.Qreg b₁ b₂ := hp (N - 1) (Nat.sub_le N 1)
    have hFw : F (F^[N - 1] s) = s' := by
      calc F (F^[N - 1] s) = F^[N - 1 + 1] s := (Function.iterate_succ_apply' F (N - 1) s).symm
        _ = F^[N] s := by rw [Nat.sub_add_cancel hN]
        _ = s' := h
    have hlt : (F^[N - 1] s).re < x₀ := hs'.2.2 _ hmem hFw
    have hmono := iter_re_mono (b₁ := b₁) (b₂ := b₂) hF (piece_mono hp (Nat.sub_le N 1))
    have hsre : x₀ ≤ s.re := fund_re_ge hs
    have hnonneg : (0 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) * (31 / 32) := by positivity
    linarith

end Fundamental

section Existence

/-- **Existence of the orbit coordinate.**  Every `z ∈ 𝒬` has a fundamental-strip representative
together with a normalised signed level: Shishikura's A.2.1(i) produces `s` in the fundamental strip
and `k` with `F^[k] z = s` (then the level is `-k`) or `F^[k] s = z` (then the level is `k`). -/
theorem exists_spec {z : ℂ} (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    (hz : z ∈ MandelDim.Qreg b₁ b₂) : ∃ p : ℂ × ℤ, Spec b₁ b₂ F x₀ z p := by
  obtain ⟨k, s, hs, hcase⟩ :=
    Work.Fatou.Qreg.fatouFundamental b₁ b₂ F x₀ hadm hF h₁ h₂ z hz
  rcases hcase with ⟨hpiece, hval⟩ | ⟨hpiece, hval⟩
  · -- `F^[k] z = s`: the level is `-k`
    refine ⟨(s, -(k : ℤ)), hs, 0, k, ⟨?_, piece_zero (fund_mem hs), hpiece⟩, Or.inl rfl, ?_⟩
    · simpa using hval.symm
    · simp
  · -- `F^[k] s = z`: the level is `k`
    refine ⟨(s, (k : ℤ)), hs, k, 0, ⟨?_, hpiece, piece_zero hz⟩, Or.inr rfl, ?_⟩
    · simpa using hval
    · simp

end Existence

end

end Work.Fatou.Surface
