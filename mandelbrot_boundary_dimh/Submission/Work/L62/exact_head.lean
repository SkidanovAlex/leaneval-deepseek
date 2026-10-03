import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.l62c_end
import Submission.Work.L62.model_head_down_deep
import Submission.Work.L62UP.head_model
import Submission.Work.L62UP.sep_chain_abstract
import Submission.Work.L62UP.up_aux
import Submission.Work.Horn.gholo
import Submission.Work.Parab.inversion.deriv_ne_zero_of_injOn

/-!
# L62 — the exact head of Lemma 6.2 (`Work.L62.exact_head`)

Shishikura's Lemma 6.2 (lifted `ℂ/ℤ` model).  For a parameter `β` in the box
`{0 ≤ Re β ≤ 1, |Im β| ≤ b}` the end of the chain is chosen by the *availability* of the horn
(`Work.L62.AvailableUp d hd β` / `AvailableDown d hd β`: the horn avoids the critical class of
`ĥ = d.E - β`), which by `Work.L62.avail_up` / `avail_down` forces the sign of `Im β` in the
direction of that end, and the amount of drift is bounded below by `κ > 0`.

The argument below uses the availability *only* (the chain produced by the head lemmas of the
area marches to the chosen end as soon as the end is available); the explicit drift bound `κ` of
the statement is not needed.

Given disc chains for `ĥ = d.E - β` in a fixed compact `K ⊆ hd.Bu` (resp. `hd.Bl`) —
`Work.L62UP.head_model_up` (upper end, arbitrary depth) and `Work.L62.model_head_down_deep`
(lower end, arbitrary depth and with the quantitative `ℤ`-separation of the discs) — this file
extracts from them the **point chain** `z` of the theorem: `z 0 = ζ ∈ {ζa, ζb}` is the (unique)
point of `W 0` of the chain, `z j ∈ W j` with `d.E (z j) - β = z (j-1)`, the *first* index `j₀`
with `s * Im (z j₀) > Y + 1` is reached (`s = ±1`: the direction of the end), and all the points
`z 0, …, z j₀` are pairwise distinct modulo `ℤ` (a consequence of the `ℤ`-separation of the
discs).

The upper end needs the separation engine `Work.L62.sep_chain_abstract` applied to
`Work.L62UP.head_model_up` (`Work.L62.head_up_deep` below); the lower end reads the separation off
`Work.L62.model_head_down_deep` directly.

The key elementary input (for `0 < j₀`) is that a point outside `d.DE` satisfies
`|Im ·| ≤ d.η₀` (`ParabData.ends_sub`: the domain contains `{η₀ < |Im ·|}`), so the starting
point of the chain is always in the strip of radius `η₀ < Y < Y + 1` around the real axis.
-/

namespace Work.L62

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-! ## 1. Elementary facts -/

/-- A point outside the maximal lift domain `d.DE` lies in the strip `|Im ·| ≤ η₀`
(`ParabData.ends_sub`: `{|Im| > η₀} ⊆ d.DE`). -/
theorem abs_im_le_eta0_of_not_mem_DE (d : MandelDim.ParabData g₀ D) {z : ℂ} (hz : z ∉ d.DE) :
    |z.im| ≤ d.η₀ := by
  by_contra h
  rw [not_le] at h
  exact hz ⟨(d.ends_sub z h).1, (d.ends_sub z h).2⟩

/-! ## 2. The point chain inside a disc chain -/

/-- **A point chain inside a disc chain.**  If `W` is a backward chain of discs for
`ĥ = d.E - β` (`ĥ '' W (j+1) = W j` injectively) and `ζ ∈ W 0`, then there is a point chain `z`
with `z 0 = ζ`, `z j ∈ W j` and `ĥ (z j) = z (j-1)`. -/
private theorem exists_point_chain {g₀ : ℂ → ℂ} {D : Set ℂ} {d : MandelDim.ParabData g₀ D}
    {β ζ : ℂ} {W : ℕ → Set ℂ} {J : ℕ} (hζ : ζ ∈ W 0)
    (hchain : ∀ j, j < J → Set.InjOn (fun w => d.E w - β) (W (j + 1)) ∧
      (fun w => d.E w - β) '' W (j + 1) = W j) :
    ∃ z : ℕ → ℂ, z 0 = ζ ∧
      ∀ j, j < J → z (j + 1) ∈ W (j + 1) ∧ d.E (z (j + 1)) - β = z j := by
  classical
  let step : ℕ → ℂ → ℂ := fun k zk =>
    if h : ∃ w ∈ W (k + 1), d.E w - β = zk then Classical.choose h else 0
  let z : ℕ → ℂ := fun n => Nat.rec (motive := fun _ => ℂ) ζ step n
  have hz0 : z 0 = ζ := rfl
  have hzsucc : ∀ k : ℕ, z (k + 1) = step k (z k) := by intro k; rfl
  have key : ∀ n, n < J → z (n + 1) ∈ W (n + 1) ∧ d.E (z (n + 1)) - β = z n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have hzn : z n ∈ W n := by
        rcases Nat.eq_zero_or_pos n with hn0 | hnpos
        · subst hn0; rw [hz0]; exact hζ
        · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hnpos)
          exact (ih m (by omega) (by omega)).1
      have hex : ∃ w ∈ W (n + 1), d.E w - β = z n := by
        have hmem : z n ∈ (fun w => d.E w - β) '' W (n + 1) := by
          rw [(hchain n hn).2]; exact hzn
        exact hmem
      have hzn1 : z (n + 1) = Classical.choose hex := by
        rw [hzsucc n]
        show (if h : ∃ w ∈ W (n + 1), d.E w - β = z n then Classical.choose h else 0)
          = Classical.choose hex
        rw [dite_eq_left hex]
      rw [hzn1]
      exact Classical.choose_spec hex
  exact ⟨z, hz0, key⟩

/-- **The level-`0` separation of a small ball about a centre from a compactum modulo `ℤ`.** -/
private theorem level_zero_sep {K : Set ℂ} {ζc : ℂ} {εc ρ ε₀ : ℝ} {W : ℕ → Set ℂ} {J : ℕ}
    (hρ : ρ ≤ εc / 2) (hεc : ∀ k : ℤ, ∀ v ∈ K, εc ≤ ‖(ζc - (k : ℂ)) - v‖)
    (hW0 : W 0 = Metric.ball ζc ρ) (hWK : ∀ j, 1 ≤ j → j ≤ J → W j ⊆ K)
    (hε₀ : ε₀ ≤ εc / 2) :
    ∀ m, 1 ≤ m → m ≤ J → ∀ u ∈ W 0, ∀ v ∈ W m, ∀ k : ℤ, ε₀ ≤ ‖u - v - (k : ℂ)‖ := by
  intro m hm1 hmJ u hu v hv k
  have hu' : ‖u - ζc‖ < ρ := by
    rw [hW0] at hu
    simpa [Metric.mem_ball, dist_eq_norm] using hu
  have hvK : v ∈ K := hWK m hm1 hmJ hv
  have h1 : εc ≤ ‖(ζc - (k : ℂ)) - v‖ := hεc k v hvK
  have h2 : ‖(ζc - (k : ℂ)) - v‖ ≤ ‖u - v - (k : ℂ)‖ + ‖u - ζc‖ := by
    have heq : (ζc - (k : ℂ)) - v = (u - v - (k : ℂ)) - (u - ζc) := by ring
    rw [heq]
    exact norm_sub_le _ _
  linarith

/-! ## 3. The first passage of the level `Y + 1` along the point chain -/

/-- **The point chain of Lemma 6.2 out of a disc chain.**  Given a backward chain of discs `W`
for `ĥ = d.E - β` whose discs `W 1, …, W J` lie in a compactum `K` (for each of which
`deriv (d.E) ≠ 0` is then automatic), whose discs are pairwise separated by `εsep` modulo `ℤ`,
whose last disc is beyond the level `Y + 1` in the direction `s = ±1`, and whose starting point
`ζ ∉ d.DE` lies in `W 0`, the point chain of `ζ` first crosses the level `Y + 1` at some `j₀ > 0`
and its points are pairwise distinct modulo `ℤ`. -/
theorem head_chain_conclusion {g₀ : ℂ → ℂ} {D : Set ℂ} {d : MandelDim.ParabData g₀ D}
    {β ζ : ℂ} {W : ℕ → Set ℂ} {Y s εsep : ℝ} {K : Set ℂ} {J : ℕ}
    (hs : s = 1 ∨ s = -1) (hY : d.η₀ < Y) (hεsep : 0 < εsep) (hJpos : 0 < J)
    (hζDE : ζ ∉ d.DE) (hζmem : ζ ∈ W 0)
    (hopen : ∀ j, j ≤ J → IsOpen (W j)) (hKDE : K ⊆ d.DE)
    (hchain : ∀ j, j < J → Set.InjOn (fun w => d.E w - β) (W (j + 1)) ∧
      (fun w => d.E w - β) '' W (j + 1) = W j)
    (hWK : ∀ j, 1 ≤ j → j ≤ J → W j ⊆ K)
    (hsep : ∀ i j, i ≤ J → j ≤ J → i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j, ∀ k : ℤ,
      εsep ≤ ‖u - v - (k : ℂ)‖)
    (hdepth : ∀ w ∈ W J, Y + 1 < s * w.im) :
    ∃ j₀ : ℕ, 0 < j₀ ∧ ∃ z : ℕ → ℂ, z 0 = ζ ∧
      (∀ j, 1 ≤ j → j ≤ j₀ → z j ∈ d.DE ∧ d.E (z j) - β = z (j - 1) ∧ deriv d.E (z j) ≠ 0) ∧
      Y + 1 < s * (z j₀).im ∧ (∀ j, j < j₀ → s * (z j).im ≤ Y + 1) ∧
      (∀ i j, i ≤ j₀ → j ≤ j₀ → i ≠ j → ∀ k : ℤ, z i ≠ z j + (k : ℂ)) := by
  classical
  obtain ⟨z, hz0, hzstep⟩ := exists_point_chain (d := d) (β := β) (W := W) (J := J) hζmem hchain
  have hzin : ∀ i, i ≤ J → z i ∈ W i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0; rw [hz0]; exact hζmem
    · have h := (hzstep (i - 1) (by omega)).1
      rwa [Nat.sub_add_cancel hipos] at h
  -- the first passage of the level
  have hex : ∃ j, j ≤ J ∧ Y + 1 < s * (z j).im :=
    ⟨J, le_rfl, hdepth (z J) (hzin J le_rfl)⟩
  have hj₀J : Nat.find hex ≤ J := (Nat.find_spec hex).1
  have hj₀deep : Y + 1 < s * (z (Nat.find hex)).im := (Nat.find_spec hex).2
  have hj₀min : ∀ j, j < Nat.find hex → s * (z j).im ≤ Y + 1 := by
    intro j hj
    have h := Nat.find_min hex hj
    have hjJ : j ≤ J := le_trans (le_of_lt hj) hj₀J
    by_contra hcon
    exact h ⟨hjJ, lt_of_not_ge hcon⟩
  -- `j₀ > 0`, because the chain starts in the strip `|Im ·| ≤ η₀ < Y + 1`
  have hj₀pos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · exfalso
      have hstrip : |ζ.im| ≤ d.η₀ := abs_im_le_eta0_of_not_mem_DE d hζDE
      have hz0' : z (Nat.find hex) = ζ := by rw [h0]; exact hz0
      have hsabs : s * ζ.im ≤ |ζ.im| := by
        rcases hs with rfl | rfl
        · simpa using le_abs_self ζ.im
        · simpa using neg_le_abs ζ.im
      rw [hz0'] at hj₀deep
      linarith
    · exact hpos
  refine ⟨Nat.find hex, hj₀pos, z, hz0, ?_, hj₀deep, hj₀min, ?_⟩
  · intro j hj1 hjJ
    have hjJ' : j ≤ J := le_trans hjJ hj₀J
    have hzj : z j ∈ W j := hzin j hjJ'
    have hrel : d.E (z j) - β = z (j - 1) := by
      have h := (hzstep (j - 1) (by omega)).2
      rwa [Nat.sub_add_cancel hj1] at h
    refine ⟨hKDE (hWK j hj1 hjJ' hzj), hrel, ?_⟩
    have hinj : Set.InjOn (fun w => d.E w - β) (W j) := by
      have h := (hchain (j - 1) (by omega)).1
      rwa [Nat.sub_add_cancel hj1] at h
    have hdiff : DifferentiableOn ℂ (fun w => d.E w - β) (W j) :=
      ((Work.Horn.differentiableOn_E d).mono
        (fun w hw => hKDE (hWK j hj1 hjJ' hw))).sub_const β
    have hder := Work.Parab.inversion.deriv_ne_zero_of_injOn (hopen j hjJ') hdiff hinj (z j) hzj
    rwa [deriv_sub_const (f := d.E) β] at hder
  · intro i j hi hj hij k hcon
    have hle := hsep i j (le_trans hi hj₀J) (le_trans hj hj₀J) hij (z i) (hzin i (le_trans hi hj₀J))
      (z j) (hzin j (le_trans hj hj₀J)) k
    rw [hcon] at hle
    simp at hle
    linarith

/-! ## 4. The upper-end head with prescribed depth and `ℤ`-separation -/

/-- **Upper-end model head at depth `Y` inside a fixed compact `K ⊆ hd.Bu`, with the discs
pairwise separated modulo `ℤ`** — the upper-end mirror of `Work.L62.model_head_down_deep`.

`Work.L62UP.head_model_up` supplies the chain (`W 0 = ball ζa ρ ∨ ball ζb ρ`,
`ĥ : W (j+1) → W j` bijectively, `W j ⊆ K` for `1 ≤ j ≤ J`, `W J` beyond depth `Y`) inside a fixed
compact `K ⊆ hd.Bu`; the separation comes from `Work.L62.sep_chain_abstract` applied to
`ĥ = d.E - β`, `O = hd.Bu`, with the collar `K + ball 0 δ ⊆ hd.Bu` and the derivative bound `Δ`
on it (`deriv d.E` is holomorphic on the open `hd.Bu`), the `T`-equivariance `E_add_int_Bu`, and
the level-`0` separation `level_zero_sep` fed by `Work.L62.dist_int_translate_pos_up` for the two
possible centres. -/
theorem head_up_deep {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {b Y : ℝ} (hb : 0 < b) (hY : d.η₀ < Y)
    {ζa ζb : ℂ} (hζa : ζa ∉ d.DE) (hζb : ζb ∉ d.DE) (hsep : ∀ k : ℤ, ζa ≠ ζb + (k : ℂ)) :
    ∃ (ρ₀ : ℝ) (K : Set ℂ) (εsep : ℝ) (J : ℕ),
      0 < ρ₀ ∧ IsCompact K ∧ K ⊆ hd.Bu ∧ 0 < εsep ∧ 0 < J ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ β : ℂ, 0 ≤ β.re → β.re ≤ 1 → |β.im| ≤ b →
        AvailableUp d hd β →
        ∃ W : ℕ → Set ℂ,
          (W 0 = Metric.ball ζa ρ ∨ W 0 = Metric.ball ζb ρ) ∧
          (∀ j, j ≤ J → IsOpen (W j) ∧ IsConnected (W j)) ∧
          (∀ j, j < J → Set.InjOn (fun w => d.E w - β) (W (j + 1)) ∧
            (fun w => d.E w - β) '' W (j + 1) = W j) ∧
          (∀ j, 1 ≤ j → j ≤ J → W j ⊆ K) ∧
          (∀ i j, i ≤ J → j ≤ J → i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j, ∀ k : ℤ,
            εsep ≤ ‖u - v - (k : ℂ)‖) ∧
          (∀ w ∈ W J, Y < w.im) := by
  classical
  obtain ⟨ρ₁, K, J, _σ, _H, hρ₁, hKc, hKBu, hJpos, _hσ, _hσc, _hσp, _hHp, hhead⟩ :=
    Work.L62.Work.L62.head_model_up d hd hb hζa hζb hsep (Y := Y) hY
  -- the two separation constants attached to the two possible centres
  obtain ⟨εa, hεa, hεa'⟩ := dist_int_translate_pos_up d hd hζa hKc hKBu
  obtain ⟨εb, hεb, hεb'⟩ := dist_int_translate_pos_up d hd hζb hKc hKBu
  set ε₀ : ℝ := min (εa / 2) (εb / 2) with hε₀def
  have hε₀ : 0 < ε₀ := lt_min (by linarith) (by linarith)
  set ρ₀ : ℝ := min ρ₁ ε₀ with hρ₀def
  have hρ₀ : 0 < ρ₀ := lt_min hρ₁ hε₀
  -- a collar of `K` inside the open horn, and a derivative bound on it
  obtain ⟨δ, hδ, hδsub⟩ := hKc.exists_cthickening_subset_open hd.Bu_open hKBu
  have hderivBu : DifferentiableOn ℂ (deriv d.E) hd.Bu :=
    ((Work.Horn.differentiableOn_E d).mono (fun w hw => hd.sub (Or.inl hw))).deriv hd.Bu_open
  obtain ⟨M, hM⟩ := (hKc.cthickening (r := δ)).exists_bound_of_continuousOn
    (hderivBu.continuousOn.mono hδsub)
  set Δ : ℝ := max 1 M with hΔdef
  have hΔ1 : 1 ≤ Δ := le_max_left 1 M
  have hmem_thick : ∀ v ∈ K, ∀ z : ℂ, ‖z‖ ≤ δ → v + z ∈ Metric.cthickening δ K := by
    intro v hv z hz
    refine Metric.closedBall_subset_cthickening hv δ ?_
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact hz
  have hKδ : ∀ v ∈ K, ∀ z : ℂ, ‖z‖ ≤ δ → v + z ∈ hd.Bu :=
    fun v hv z hz => hδsub (hmem_thick v hv z hz)
  have hΔbd : ∀ v ∈ K, ∀ z : ℂ, ‖z‖ ≤ δ → ‖deriv d.E (v + z)‖ ≤ Δ :=
    fun v hv z hz => le_trans (hM (v + z) (hmem_thick v hv z hz)) (le_max_right 1 M)
  refine ⟨ρ₀, K, min ε₀ δ / (2 * Δ ^ J), J, hρ₀, hKc, hKBu, ?_, hJpos, ?_⟩
  · exact div_pos (lt_min hε₀ hδ) (by positivity)
  · intro ρ hρ hρρ₀ β hβ0 hβ1 hβim hav
    obtain ⟨W, hW0, hWoc, hchain, hWK, _hWsig, _hWbdd, hWdeep⟩ :=
      hhead ρ hρ (le_trans hρρ₀ (min_le_left _ _)) β hβ0 hβ1 hβim hav
    -- `ρ` is at most half of each of the two level-`0` constants
    have hρa : ρ ≤ εa / 2 :=
      le_trans (le_trans hρρ₀ (min_le_right _ _)) (min_le_left _ _)
    have hρb : ρ ≤ εb / 2 :=
      le_trans (le_trans hρρ₀ (min_le_right _ _)) (min_le_right _ _)
    have hε₀a : ε₀ ≤ εa / 2 := min_le_left _ _
    have hε₀b : ε₀ ≤ εb / 2 := min_le_right _ _
    -- `ĥ = d.E - β` is holomorphic and `T`-equivariant on the horn
    have hFd : DifferentiableOn ℂ (fun w => d.E w - β) hd.Bu :=
      ((Work.Horn.differentiableOn_E d).mono (fun w hw => hd.sub (Or.inl hw))).sub_const β
    have hT : ∀ w ∈ hd.Bu, ∀ k : ℤ,
        (fun u => d.E u - β) (w + (k : ℂ)) = (fun u => d.E u - β) w + (k : ℂ) := by
      intro w hw k
      show d.E (w + (k : ℂ)) - β = (d.E w - β) + (k : ℂ)
      rw [E_add_int_Bu d hd hw k]
      ring
    -- the separation for the relevant centre
    have main : ∀ ζc : ℂ, (ζc = ζa ∨ ζc = ζb) → W 0 = Metric.ball ζc ρ →
        ∀ i j, i ≤ J → j ≤ J → i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j, ∀ k : ℤ,
          min ε₀ δ / (2 * Δ ^ J) ≤ ‖u - v - (k : ℂ)‖ := by
      intro ζc hζc hW0c
      have hsep0 : ∀ m, 1 ≤ m → m ≤ J → ∀ u ∈ W 0, ∀ v ∈ W m, ∀ k : ℤ,
          ε₀ ≤ ‖u - v - (k : ℂ)‖ := by
        rcases hζc with h | h
        · rw [h] at hW0c
          exact level_zero_sep (εc := εa) hρa hεa' hW0c hWK hε₀a
        · rw [h] at hW0c
          exact level_zero_sep (εc := εb) hρb hεb' hW0c hWK hε₀b
      exact sep_chain_abstract (F := fun w => d.E w - β) (K := K) (O := hd.Bu) (ζc := ζc)
        (W := W) (J := J) hρ hε₀ hδ hΔ1 hd.Bu_open hFd hT hKδ
        (fun v hv z hz => by rw [deriv_sub_const (f := d.E) β]; exact hΔbd v hv z hz)
        hchain hW0c hWK hsep0
    rcases hW0 with hWa | hWb
    · exact ⟨W, Or.inl hWa, hWoc, hchain, hWK, main ζa (Or.inl rfl) hWa, hWdeep⟩
    · exact ⟨W, Or.inr hWb, hWoc, hchain, hWK, main ζb (Or.inr rfl) hWb, hWdeep⟩

/-! ## 5. The theorem -/

theorem exact_head {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {b κ : ℝ} (hb : 0 < b) (hκ : 0 < κ) {cl : ℂ}
    (hcl : Filter.Tendsto (fun w => d.E w - w) MandelDim.lowerEnd (nhds cl))
    {ζa ζb : ℂ} (hζa : ζa ∉ d.DE) (hζb : ζb ∉ d.DE) (hsep : ∀ k : ℤ, ζa ≠ ζb + (k : ℂ))
    {Y : ℝ} (hY : d.η₀ < Y) :
    ∀ β : ℂ, 0 ≤ β.re → β.re ≤ 1 → |β.im| ≤ b → ∀ s : ℝ,
      ((s = 1 ∧ Work.L62.AvailableUp d hd β ∧ κ ≤ β.im) ∨
        (s = -1 ∧ Work.L62.AvailableDown d hd β ∧ κ ≤ cl.im - β.im)) →
      ∃ ζ : ℂ, (ζ = ζa ∨ ζ = ζb) ∧ ∃ j₀ : ℕ, 0 < j₀ ∧ ∃ z : ℕ → ℂ, z 0 = ζ ∧
        (∀ j, 1 ≤ j → j ≤ j₀ → z j ∈ d.DE ∧ d.E (z j) - β = z (j - 1) ∧ deriv d.E (z j) ≠ 0) ∧
        Y + 1 < s * (z j₀).im ∧ (∀ j, j < j₀ → s * (z j).im ≤ Y + 1) ∧
        (∀ i j, i ≤ j₀ → j ≤ j₀ → i ≠ j → ∀ k : ℤ, z i ≠ z j + (k : ℂ)) := by
  intro β hβ0 hβ1 hβim s hs
  rcases hs with ⟨rfl, hav, _hκβ⟩ | ⟨rfl, hav, _hκcl⟩
  · -- ### the upper end
    obtain ⟨ρ₀, K, εsep, J, hρ₀, hKc, hKBu, hεsep, hJpos, hhead⟩ :=
      head_up_deep (Y := Y + 1) d hd hb (by linarith) hζa hζb hsep
    obtain ⟨W, hW0, hWoc, hchain, hWK, hsepW, hWdeep⟩ :=
      hhead ρ₀ hρ₀ le_rfl β hβ0 hβ1 hβim hav
    rcases hW0 with hWa | hWb
    · refine ⟨ζa, Or.inl rfl, ?_⟩
      have hζmem : ζa ∈ W 0 := by rw [hWa]; exact Metric.mem_ball_self hρ₀
      obtain ⟨j₀, hj₀pos, z, hz0, hchainz, hdeep, hmin, hdist⟩ :=
        head_chain_conclusion (d := d) (β := β) (W := W) (Y := Y) (s := 1) (K := K) (J := J)
          (Or.inl rfl) hY hεsep hJpos hζa hζmem (fun j hj => (hWoc j hj).1)
          (fun w hw => hd.sub (Or.inl (hKBu hw))) hchain hWK hsepW
          (fun w hw => by have h := hWdeep w hw; simpa using h)
      exact ⟨j₀, hj₀pos, z, hz0, hchainz, hdeep, hmin, hdist⟩
    · refine ⟨ζb, Or.inr rfl, ?_⟩
      have hζmem : ζb ∈ W 0 := by rw [hWb]; exact Metric.mem_ball_self hρ₀
      obtain ⟨j₀, hj₀pos, z, hz0, hchainz, hdeep, hmin, hdist⟩ :=
        head_chain_conclusion (d := d) (β := β) (W := W) (Y := Y) (s := 1) (K := K) (J := J)
          (Or.inl rfl) hY hεsep hJpos hζb hζmem (fun j hj => (hWoc j hj).1)
          (fun w hw => hd.sub (Or.inl (hKBu hw))) hchain hWK hsepW
          (fun w hw => by have h := hWdeep w hw; simpa using h)
      exact ⟨j₀, hj₀pos, z, hz0, hchainz, hdeep, hmin, hdist⟩
  · -- ### the lower end
    obtain ⟨ρ₀, K, _C₀, εsep, J, hρ₀, hKc, hKBl, _hC₀, hεsep, hJpos, hhead⟩ :=
      model_head_down_deep (M := Y + 1) d hd hcl hb (by linarith) hζa hζb hsep
    obtain ⟨W, hW0, hWoc, hchain, hWK, hsepW, _hbdd, _hdiam, _hC0, hWdeep⟩ :=
      hhead ρ₀ hρ₀ le_rfl β hβ0 hβ1 hβim hav
    rcases hW0 with hWa | hWb
    · refine ⟨ζa, Or.inl rfl, ?_⟩
      have hζmem : ζa ∈ W 0 := by rw [hWa]; exact Metric.mem_ball_self hρ₀
      obtain ⟨j₀, hj₀pos, z, hz0, hchainz, hdeep, hmin, hdist⟩ :=
        head_chain_conclusion (d := d) (β := β) (W := W) (Y := Y) (s := -1) (K := K) (J := J)
          (Or.inr rfl) hY hεsep hJpos hζa hζmem (fun j hj => (hWoc j hj).1)
          (fun w hw => hd.sub (Or.inr (hKBl hw))) hchain hWK hsepW
          (fun w hw => by have h := hWdeep w hw; simp only [neg_one_mul]; linarith)
      exact ⟨j₀, hj₀pos, z, hz0, hchainz, hdeep, hmin, hdist⟩
    · refine ⟨ζb, Or.inr rfl, ?_⟩
      have hζmem : ζb ∈ W 0 := by rw [hWb]; exact Metric.mem_ball_self hρ₀
      obtain ⟨j₀, hj₀pos, z, hz0, hchainz, hdeep, hmin, hdist⟩ :=
        head_chain_conclusion (d := d) (β := β) (W := W) (Y := Y) (s := -1) (K := K) (J := J)
          (Or.inr rfl) hY hεsep hJpos hζb hζmem (fun j hj => (hWoc j hj).1)
          (fun w hw => hd.sub (Or.inr (hKBl hw))) hchain hWK hsepW
          (fun w hw => by have h := hWdeep w hw; simp only [neg_one_mul]; linarith)
      exact ⟨j₀, hj₀pos, z, hz0, hchainz, hdeep, hmin, hdist⟩

end

end Work.L62
