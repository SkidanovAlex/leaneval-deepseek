import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilCrux.pathPieceEstimate

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilCrux

/-!
## N4c5, the parameter-direction step of the G4c crux (`PathGainBound`)

`PathGainBound` is the pure real-analysis node N4c5 of `sources/wilkiesG4/wilkies_g4c_crux_map.md`.
The proof is a shifted Euler telescoping along the path `s ↦ (w₁ + s • e_i, ψ s)`:

* the *single-piece* estimate (`Work.WilCrux.pathPieceEstimate`) gives, on every break-free
  interval and between two interior points,
  `F y - F x ≥ η(y - x) - 2bMτ` for the path function `F`;
* the breaks of `brk` are used as nodes: around a node `t` only the *shifted* values `F(t±ε)`
  appear, so one node costs at most `M‖ψ(t+ε)‖ + M‖ψ(t-ε)‖ ≤ 2Mτ` (via `hsmall`), and the
  endpoints `0, L` cost at most `Mτ` each;
* the `ε → 0` limit is taken with `le_of_tendsto` on `𝓝[>] 0` (the admissible `ε` form a
  neighbourhood of `0`, by `eventually_lt_finset` and the finiteness of `brk`).

Summing over `≤ K+1` pieces and `≤ K+2` nodes gives
`ηL ≤ 2Mτ + 2Mbτ(K+1) + 2Mτ(K+2)`, which is `≤ (K+2)(2(b+1)M+1)τ`.
-/

/-- Finitely many strict conditions `ε < c x` (with `0 < c x`) hold eventually on `Ioi 0`. -/
private lemma eventually_lt_finset {α : Type*} (T : Finset α) (c : α → ℝ)
    (hc : ∀ x ∈ T, 0 < c x) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ T, ε < c x := by
  revert hc c
  refine Finset.induction_on T ?_ ?_
  · intro c hc
    simp
  · intro x T' hxT ih c hc
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < c x := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < c x from hc x (Finset.mem_insert_self x T'))]
        with ε hε
      exact hε.2
    have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ T', ε < c x :=
      ih c (fun x hx => hc x (Finset.mem_insert_of_mem hx))
    filter_upwards [h1, h2] with ε hε1 hε2 x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rwa [h]
    · exact hε2 x h

/-- **N4c5 (the parameter-direction step, pure analysis).** Along the path
`s ↦ (w1 + s e_i, psi s)`, with `||psi s|| <= tau`, piecewise `C^1` and coordinatewise monotone
off at most `K` break points, if the directional derivative of `G` in the direction `e_i` is at
least `eta` on the path, `G` is `M`-Lipschitz in the fibre variable on the `tau`-ball *along the
path*, and `|G w z| <= M ||z||` there, then the gain `eta * L` is `O(tau)`.

Proof: on each of the at most `K+1` pieces the function `s ↦ G(w1+s e_i, psi s)` has derivative
`fderiv (famFun G) (...) (e_i (+) 0) + sum_k (fibre partial_k)(psi_k')`, which is
`>= eta - M * sum_k |psi_k'|` (gain hypothesis; the Lipschitz bound bounds the fibre partials by
`M`).  The monotone coordinates give total variation `<= 2 tau` per coordinate per piece, a break
costs at most `2 M tau` (Lipschitz in `z`: use *increments*, no `+tau` term), and the endpoints
cost `|G| <= M tau` each. -/
theorem PathGainBound {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (i : Fin a)
    (w₁ : Fin a → ℝ) (L τ M η : ℝ) (hL : 0 < L) (hτ : 0 < τ) (hM : 0 ≤ M)
    (ψ : ℝ → (Fin b → ℝ)) (K : ℕ) (brk : Finset ℝ) (hbrk : brk.card ≤ K)
    (hsph : ∀ s ∈ Set.Icc 0 L, ‖ψ s‖ ≤ τ)
    (hdiff : ∀ s ∈ Set.Ioo 0 L, s ∉ brk → DifferentiableAt ℝ ψ s)
    (hmono : ∀ k : Fin b, ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ L →
      (∀ u ∈ Set.Ioo s t, u ∉ brk) →
      MonotoneOn (fun u => ψ u k) (Set.Ioo s t) ∨ AntitoneOn (fun u => ψ u k) (Set.Ioo s t))
    (hLip : ∀ s ∈ Set.Icc 0 L, ∀ z z' : Fin b → ℝ, ‖z‖ ≤ τ → ‖z'‖ ≤ τ →
      |G (w₁ + s • Pi.single i 1) z - G (w₁ + s • Pi.single i 1) z'| ≤ M * ‖z - z'‖)
    (hsmall : ∀ s ∈ Set.Icc 0 L, ∀ z : Fin b → ℝ, ‖z‖ ≤ τ →
      |G (w₁ + s • Pi.single i 1) z| ≤ M * ‖z‖)
    (hC1 : ∀ s ∈ Set.Icc 0 L, ContDiffAt ℝ 1 (Work.WilG4c.famFun G)
      (Fin.append (w₁ + s • Pi.single i 1) (ψ s)))
    (hgain : ∀ s ∈ Set.Icc 0 L, η ≤ fderiv ℝ (Work.WilG4c.famFun G)
      (Fin.append (w₁ + s • Pi.single i 1) (ψ s)) (Fin.append (Pi.single i 1) 0)) :
    η * L ≤ ((K : ℝ) + 2) * (2 * ((b : ℝ) + 1) * M + 1) * τ := by
  have hfam : ∀ (w : Fin a → ℝ) (z : Fin b → ℝ), Work.WilG4c.famFun G (Fin.append w z) = G w z :=
    fun w z => by simp only [Work.WilG4c.famFun, Fin.append_left, Fin.append_right]
  set S : Finset ℝ := brk.filter (fun x => 0 < x ∧ x < L) with hSdef
  have hSsub : ∀ x ∈ S, x ∈ brk := fun x hx => (Finset.mem_filter.mp hx).1
  have hSpos : ∀ x ∈ S, 0 < x ∧ x < L := fun x hx => (Finset.mem_filter.mp hx).2
  have hScard : S.card ≤ K := le_trans (Finset.card_filter_le brk _) hbrk
  have hSall : ∀ x ∈ brk, 0 < x → x < L → x ∈ S := fun x hx h1 h2 => Finset.mem_filter.mpr ⟨hx, h1, h2⟩
  have piece : ∀ {l r x y : ℝ}, 0 ≤ l → l < x → x < y → y < r → r ≤ L →
      (∀ u ∈ Set.Ioo l r, u ∉ brk) →
      (∀ k : Fin b, MonotoneOn (fun u => ψ u k) (Set.Ioo l r) ∨
        AntitoneOn (fun u => ψ u k) (Set.Ioo l r)) →
      Work.WilG4c.famFun G (Fin.append (w₁ + y • Pi.single i 1) (ψ y))
        - Work.WilG4c.famFun G (Fin.append (w₁ + x • Pi.single i 1) (ψ x))
        ≥ η * (y - x) - 2 * ((b : ℝ)) * M * τ :=
    fun {l r x y} hl0 hlx hxy hyr hrL hno hmon =>
      pathPieceEstimate G i w₁ L τ M η hτ hM ψ brk hsph hdiff hLip hC1 hgain
        hl0 hlx hxy hyr hrL hno hmon
  -- ## The set of admissible `ε` is a neighbourhood of `0` in `Ioi 0`
  have hgood : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (0 < ε) ∧ (2 * ε < L) ∧ (∀ x ∈ S, 2 * ε < x) ∧
      (∀ x ∈ S, ∀ y ∈ S, x < y → 2 * ε < y - x) ∧ (∀ x ∈ S, 2 * ε < L - x) := by
    have h0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := by
      filter_upwards [self_mem_nhdsWithin] with ε hε; exact hε
    have hL' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < L / 2 := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < L / 2 by linarith)] with ε hε; exact hε.2
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ S, ε < x / 2 :=
      eventually_lt_finset S (fun x => x / 2) (fun x hx => half_pos (hSpos x hx).1)
    have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ S, ε < (L - x) / 2 :=
      eventually_lt_finset S (fun x => (L - x) / 2) (fun x hx => half_pos (by linarith [(hSpos x hx).2]))
    have h3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∀ p ∈ (S.product S).filter (fun p : ℝ × ℝ => p.1 < p.2), ε < (p.2 - p.1) / 2 :=
      eventually_lt_finset ((S.product S).filter (fun p : ℝ × ℝ => p.1 < p.2))
        (fun p : ℝ × ℝ => (p.2 - p.1) / 2) (fun p hp => by
        have hp' := Finset.mem_filter.mp hp
        exact half_pos (by linarith [hp'.2]))
    filter_upwards [h0, hL', h1, h2, h3] with ε h0 hL' h1 h2 h3
    refine ⟨h0, by linarith, fun x hx => by linarith [h1 x hx],
      fun x hx y hy hxy => by
        have := h3 (x, y) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩)
        linarith,
      fun x hx => by linarith [h2 x hx]⟩
  -- ## The main analytic estimate (accounting over the break points)
  have hkey : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      η * (L - 2 * ε * ((S.card : ℝ) + 1)) ≤ 2 * M * τ + 2 * M * (b : ℝ) * τ * ((S.card : ℝ) + 1)
        + (∑ x ∈ S, M * (‖ψ (x + ε)‖ + ‖ψ (x - ε)‖) + (M * ‖ψ ε‖ + M * ‖ψ 0‖)
          + (M * ‖ψ L‖ + M * ‖ψ (L - ε)‖)) := by
    refine hgood.mono ?_
    rintro ε ⟨hεpos, hεL, hg1, hg2, hg3⟩
    -- the shifted accounting
    have hacc : ∀ (T : Finset ℝ) (u v : ℝ), 0 ≤ u → u < v → v ≤ L → 2 * ε < v - u →
        (∀ x ∈ T, u < x ∧ x < v) → (∀ x ∈ brk, u < x → x < v → x ∈ T) →
        (∀ x ∈ T, 2 * ε < x - u) → (∀ x ∈ T, ∀ y ∈ T, x < y → 2 * ε < y - x) →
        (∀ x ∈ T, 2 * ε < v - x) →
        Work.WilG4c.famFun G (Fin.append (w₁ + (v - ε) • Pi.single i 1) (ψ (v - ε)))
          - Work.WilG4c.famFun G (Fin.append (w₁ + (u + ε) • Pi.single i 1) (ψ (u + ε)))
          ≥ η * (v - u - 2 * ε * ((T.card : ℝ) + 1)) - 2 * (b : ℝ) * M * τ * ((T.card : ℝ) + 1)
            - ∑ x ∈ T, M * (‖ψ (x + ε)‖ + ‖ψ (x - ε)‖) := by
      intro T
      refine Finset.induction_on_max T ?_ ?_
      · -- no interior breaks: a single piece
        intro u v hu huv hvL huvε hTsub hTbrk hgT1 hgT2 hgT3
        have hno : ∀ w ∈ Set.Ioo u v, w ∉ brk := by
          intro w hw hwb
          exact Finset.notMem_empty w (hTbrk w hwb hw.1 hw.2)
        have hmon : ∀ k : Fin b, MonotoneOn (fun x => ψ x k) (Set.Ioo u v) ∨
            AntitoneOn (fun x => ψ x k) (Set.Ioo u v) := fun k => hmono k u v hu huv hvL hno
        have hp := piece (l := u) (r := v) (x := u + ε) (y := v - ε) hu (by linarith) (by linarith)
          (by linarith) hvL hno hmon
        simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, sub_zero]
        linarith [hp]
      · -- peel off the largest interior break
        intro m T' hmax ih
        intro u v hu huv hvL huvε hTsub hTbrk hgT1 hgT2 hgT3
        have hmS : m ∈ insert m T' := Finset.mem_insert_self m T'
        have hmu : u < m := (hTsub m hmS).1
        have hmv : m < v := (hTsub m hmS).2
        have hmnT : m ∉ T' := fun h => absurd (hmax m h) (lt_irrefl m)
        have hm0 : 0 ≤ m := le_trans hu (le_of_lt hmu)
        -- the inductive hypothesis on the smaller interval `(u,m)`
        have hIH := ih u m hu hmu (le_trans (le_of_lt hmv) hvL) (hgT1 m hmS)
          (fun x hx => ⟨(hTsub x (Finset.mem_insert_of_mem hx)).1, hmax x hx⟩)
          (fun x hxb hux hxm => by
            rcases Finset.mem_insert.mp (hTbrk x hxb hux (lt_trans hxm hmv)) with h | h
            · exact absurd h (by linarith)
            · exact h)
          (fun x hx => hgT1 x (Finset.mem_insert_of_mem hx))
          (fun x hx y hy hxy => hgT2 x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy)
          (fun x hx => by
            have := hgT2 x (Finset.mem_insert_of_mem hx) m hmS (hmax x hx)
            linarith)
        -- the piece `(m,v)`
        have hno_mv : ∀ w ∈ Set.Ioo m v, w ∉ brk := by
          intro w hw hwb
          rcases Finset.mem_insert.mp (hTbrk w hwb (lt_trans hmu hw.1) hw.2) with h | h
          · exact absurd h (by linarith [hw.1])
          · exact absurd (hmax w h) (by linarith [hw.1])
        have hmon_mv : ∀ k : Fin b, MonotoneOn (fun x => ψ x k) (Set.Ioo m v) ∨
            AntitoneOn (fun x => ψ x k) (Set.Ioo m v) :=
          fun k => hmono k m v hm0 hmv hvL hno_mv
        have hp := piece (l := m) (r := v) (x := m + ε) (y := v - ε) hm0 (by linarith)
          (by linarith [hgT3 m hmS]) (by linarith) hvL hno_mv hmon_mv
        -- the node correction at `m`
        have hmε0 : 0 ≤ m - ε := by linarith [hgT1 m hmS]
        have hmεL : m + ε ≤ L := by linarith [hgT3 m hmS, hvL]
        have hcorr : Work.WilG4c.famFun G (Fin.append (w₁ + (m + ε) • Pi.single i 1) (ψ (m + ε)))
            - Work.WilG4c.famFun G (Fin.append (w₁ + (m - ε) • Pi.single i 1) (ψ (m - ε)))
            ≥ -(M * ‖ψ (m + ε)‖ + M * ‖ψ (m - ε)‖) := by
          have h1 : |Work.WilG4c.famFun G
              (Fin.append (w₁ + (m + ε) • Pi.single i 1) (ψ (m + ε)))| ≤ M * ‖ψ (m + ε)‖ := by
            rw [hfam]
            exact hsmall (m + ε) ⟨by linarith, hmεL⟩ (ψ (m + ε)) (hsph (m + ε) ⟨by linarith, hmεL⟩)
          have h2 : |Work.WilG4c.famFun G
              (Fin.append (w₁ + (m - ε) • Pi.single i 1) (ψ (m - ε)))| ≤ M * ‖ψ (m - ε)‖ := by
            rw [hfam]
            exact hsmall (m - ε) ⟨hmε0, by linarith⟩ (ψ (m - ε)) (hsph (m - ε) ⟨hmε0, by linarith⟩)
          linarith [neg_abs_le (Work.WilG4c.famFun G
              (Fin.append (w₁ + (m + ε) • Pi.single i 1) (ψ (m + ε)))),
            le_abs_self (Work.WilG4c.famFun G
              (Fin.append (w₁ + (m - ε) • Pi.single i 1) (ψ (m - ε)))), h1, h2]
        -- assemble
        have hcard : (((insert m T').card : ℕ) : ℝ) = ((T'.card : ℕ) : ℝ) + 1 := by
          rw [Finset.card_insert_of_notMem hmnT]
          push_cast
          ring
        rw [hcard, Finset.sum_insert hmnT]
        linarith [hIH, hp, hcorr]
    -- apply the accounting to the full set of interior breaks
    have hmain := hacc S 0 L le_rfl hL le_rfl (by linarith)
      (fun x hx => ⟨(hSpos x hx).1, (hSpos x hx).2⟩)
      (fun x hxb h1 h2 => hSall x hxb h1 h2) (fun x hx => by linarith [hg1 x hx]) hg2 hg3
    -- endpoint and boundary bounds
    have hF0 : |Work.WilG4c.famFun G (Fin.append (w₁ + (0 : ℝ) • Pi.single i 1) (ψ 0))| ≤ M * ‖ψ 0‖ := by
      rw [hfam]
      exact hsmall 0 ⟨le_rfl, le_of_lt hL⟩ (ψ 0) (hsph 0 ⟨le_rfl, le_of_lt hL⟩)
    have hFε : |Work.WilG4c.famFun G (Fin.append (w₁ + ε • Pi.single i 1) (ψ ε))| ≤ M * ‖ψ ε‖ := by
      rw [hfam]
      exact hsmall ε ⟨le_of_lt hεpos, by linarith⟩ (ψ ε) (hsph ε ⟨le_of_lt hεpos, by linarith⟩)
    have hFL : |Work.WilG4c.famFun G (Fin.append (w₁ + L • Pi.single i 1) (ψ L))| ≤ M * ‖ψ L‖ := by
      rw [hfam]
      exact hsmall L ⟨le_of_lt hL, le_rfl⟩ (ψ L) (hsph L ⟨le_of_lt hL, le_rfl⟩)
    have hFLε : |Work.WilG4c.famFun G (Fin.append (w₁ + (L - ε) • Pi.single i 1) (ψ (L - ε)))|
        ≤ M * ‖ψ (L - ε)‖ := by
      rw [hfam]
      exact hsmall (L - ε) ⟨by linarith, by linarith⟩ (ψ (L - ε)) (hsph (L - ε) ⟨by linarith, by linarith⟩)
    have hLb : |Work.WilG4c.famFun G (Fin.append (w₁ + L • Pi.single i 1) (ψ L))| ≤ M * τ :=
      le_trans hFL (mul_le_mul_of_nonneg_left (hsph L ⟨le_of_lt hL, le_rfl⟩) hM)
    have h0b : |Work.WilG4c.famFun G
        (Fin.append (w₁ + (0 : ℝ) • Pi.single i 1) (ψ 0))| ≤ M * τ :=
      le_trans hF0 (mul_le_mul_of_nonneg_left (hsph 0 ⟨le_rfl, le_of_lt hL⟩) hM)
    simp only [zero_add, sub_zero] at hmain
    have hcorr1 : Work.WilG4c.famFun G (Fin.append (w₁ + ε • Pi.single i 1) (ψ ε))
        - Work.WilG4c.famFun G (Fin.append (w₁ + (0 : ℝ) • Pi.single i 1) (ψ 0))
        ≥ -(M * ‖ψ ε‖ + M * ‖ψ 0‖) := by
      linarith [neg_abs_le (Work.WilG4c.famFun G (Fin.append (w₁ + ε • Pi.single i 1) (ψ ε))),
        le_abs_self (Work.WilG4c.famFun G (Fin.append (w₁ + (0 : ℝ) • Pi.single i 1) (ψ 0))),
        hFε, hF0]
    have hcorr2 : Work.WilG4c.famFun G (Fin.append (w₁ + L • Pi.single i 1) (ψ L))
        - Work.WilG4c.famFun G (Fin.append (w₁ + (L - ε) • Pi.single i 1) (ψ (L - ε)))
        ≥ -(M * ‖ψ L‖ + M * ‖ψ (L - ε)‖) := by
      linarith [neg_abs_le (Work.WilG4c.famFun G (Fin.append (w₁ + L • Pi.single i 1) (ψ L))),
        le_abs_self (Work.WilG4c.famFun G (Fin.append (w₁ + (L - ε) • Pi.single i 1) (ψ (L - ε)))),
        hFL, hFLε]
    have hbnd : Work.WilG4c.famFun G (Fin.append (w₁ + L • Pi.single i 1) (ψ L))
        - Work.WilG4c.famFun G (Fin.append (w₁ + (0 : ℝ) • Pi.single i 1) (ψ 0)) ≤ 2 * M * τ := by
      linarith [le_abs_self (Work.WilG4c.famFun G (Fin.append (w₁ + L • Pi.single i 1) (ψ L))),
        neg_le_abs (Work.WilG4c.famFun G (Fin.append (w₁ + (0 : ℝ) • Pi.single i 1) (ψ 0))),
        hLb, h0b]
    linarith [hmain, hcorr1, hcorr2, hbnd]
  -- ## Let `ε → 0`
  have htend : Filter.Tendsto (fun ε : ℝ => η * (L - 2 * ε * ((S.card : ℝ) + 1)))
      (𝓝[>] (0 : ℝ)) (𝓝 (η * L)) := by
    have hcont : Continuous (fun ε : ℝ => η * (L - 2 * ε * ((S.card : ℝ) + 1))) := by fun_prop
    have h := hcont.tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  by_cases hb0 : b = 0
  · -- ## The case `b = 0`: all the fibre norms below vanish
    subst hb0
    have hz : ∀ z : Fin 0 → ℝ, ‖z‖ = 0 := fun z => by rw [norm_eq_zero]; exact Subsingleton.elim _ _
    have hk : ∀ᶠ ε in 𝓝[>] (0 : ℝ), η * (L - 2 * ε * ((S.card : ℝ) + 1)) ≤ 2 * M * τ := by
      refine hkey.mono (fun ε hε => ?_)
      simp only [hz, mul_zero, add_zero, Nat.cast_zero, zero_mul, Finset.sum_const_zero] at hε ⊢
      linarith
    have hfin : η * L ≤ 2 * M * τ := le_of_tendsto htend hk
    have hsimp : ((K : ℝ) + 2) * (2 * ((↑(0 : ℕ) : ℝ) + 1) * M + 1) * τ
        = ((K : ℝ) + 2) * (2 * M + 1) * τ := by norm_num
    rw [hsimp]
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    have hcmp : 2 * M * τ ≤ ((K : ℝ) + 2) * (2 * M + 1) * τ := by
      have hMK : (0 : ℝ) ≤ (K : ℝ) * M := mul_nonneg hK0 hM
      nlinarith [hK0, hM, hτ, hMK]
    linarith
  · -- ## The main case `b ≥ 1`
    have hb1 : (1 : ℝ) ≤ (b : ℝ) := by
      have h1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb0
      exact_mod_cast h1
    have hk : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        η * (L - 2 * ε * ((S.card : ℝ) + 1)) ≤
          2 * M * τ + 2 * M * (b : ℝ) * τ * ((S.card : ℝ) + 1) + 2 * M * τ * ((S.card : ℝ) + 2) := by
      refine (hgood.and hkey).mono (fun ε hε => ?_)
      obtain ⟨⟨hεpos, hεL, hg1, hg2, hg3⟩, hεbound⟩ := hε
      have hcorrsum : ∑ x ∈ S, M * (‖ψ (x + ε)‖ + ‖ψ (x - ε)‖) ≤ 2 * M * τ * (S.card : ℝ) := by
        calc ∑ x ∈ S, M * (‖ψ (x + ε)‖ + ‖ψ (x - ε)‖)
            ≤ ∑ x ∈ S, M * (2 * τ) := by
              refine Finset.sum_le_sum (fun x hx => ?_)
              have hx1 : ‖ψ (x + ε)‖ ≤ τ :=
                hsph (x + ε) ⟨by linarith [(hSpos x hx).1], by linarith [(hSpos x hx).2, hg3 x hx]⟩
              have hx2 : ‖ψ (x - ε)‖ ≤ τ :=
                hsph (x - ε) ⟨by linarith [(hSpos x hx).1, hg1 x hx], by linarith [(hSpos x hx).2]⟩
              nlinarith [hM, hx1, hx2]
          _ = 2 * M * τ * (S.card : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
              ring
      have hA : M * ‖ψ ε‖ ≤ M * τ :=
        mul_le_mul_of_nonneg_left (hsph ε ⟨le_of_lt hεpos, by linarith⟩) hM
      have hB : M * ‖ψ 0‖ ≤ M * τ :=
        mul_le_mul_of_nonneg_left (hsph 0 ⟨le_rfl, le_of_lt hL⟩) hM
      have hC : M * ‖ψ L‖ ≤ M * τ :=
        mul_le_mul_of_nonneg_left (hsph L ⟨le_of_lt hL, le_rfl⟩) hM
      have hD : M * ‖ψ (L - ε)‖ ≤ M * τ :=
        mul_le_mul_of_nonneg_left (hsph (L - ε) ⟨by linarith, by linarith⟩) hM
      linarith [hεbound, hcorrsum, hA, hB, hC, hD]
    have hfin : η * L ≤ 2 * M * τ + 2 * M * (b : ℝ) * τ * ((S.card : ℝ) + 1)
        + 2 * M * τ * ((S.card : ℝ) + 2) := le_of_tendsto htend hk
    have hcast : ((S.card : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hScard
    have hstep1 : 2 * M * τ + 2 * M * (b : ℝ) * τ * ((S.card : ℝ) + 1) + 2 * M * τ * ((S.card : ℝ) + 2)
        ≤ 2 * M * τ + 2 * M * (b : ℝ) * τ * ((K : ℝ) + 1) + 2 * M * τ * ((K : ℝ) + 2) := by
      have h1 : (0 : ℝ) ≤ 2 * M * (b : ℝ) * τ := by positivity
      have h2 : (0 : ℝ) ≤ 2 * M * τ := by positivity
      nlinarith [hcast]
    have hstep2 : 2 * M * τ + 2 * M * (b : ℝ) * τ * ((K : ℝ) + 1) + 2 * M * τ * ((K : ℝ) + 2)
        ≤ ((K : ℝ) + 2) * (2 * ((b : ℝ) + 1) * M + 1) * τ := by
      have h1 : (0 : ℝ) ≤ M * ((b : ℝ) - 1) := mul_nonneg hM (by linarith)
      have h2 : (0 : ℝ) ≤ M * ((b : ℝ) - 1) * τ := mul_nonneg h1 (le_of_lt hτ)
      nlinarith [h2]
    linarith [hfin, hstep1, hstep2]

end Work.WilCrux
