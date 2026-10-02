import Submission.Work.Deep.Nibble.r2_own_asm
import Submission.Work.Deep.Nibble.r2_Wv_mean
import Submission.Work.Deep.Nibble.r2_Y_mean
import Submission.Work.Deep.Nibble.r2_S_mean

set_option maxHeartbeats 1000000

namespace Work.Deep.Nibble

/-- **One round of the Rödl nibble (the "wasteful" variant), corrected level.**

Keep each edge of the `r`-uniform linear hypergraph `𝓖` independently with probability
`p = θ/D`; let `X` be the kept edges, `covX = ⋃X`, and let the residual hypergraph `𝓖'` be
induced on `residV = V ∖ covX`.  Then some outcome satisfies `RoundGood`:
`|X| ∈ (1±δ)|𝓖|θ/D`; `|covX| ∈ (1±δ)(1-e^{-θ})|V|`; `S = Σ_u k_u 1[k_u ≥ 2] ≤ (1+δ)(θ-θe^{-θ})|V|`
(`k_u` = number of kept edges through `u`); and every *uncovered* vertex has residual degree
within `(1±ε')` of `D' = D(1-θ/D)^{(r-1)(D-1)}`, provided `ε' ≥ 100(ε + ε r θ)`.

All definitions are in `Submission/Work/Deep/Nibble/exists_matching_covering_most.lean`
(read it).

*Proof ingredients.* (1) `Ω = ∏_{e : 𝓖} Bool` with independent weights `(1-p,p)`; the
coordinates are the edges. (2) Exact expectations: `E|X| = |𝓖|p`; for a vertex `u` the edges
through `u` are distinct and pairwise meet only at `u` (linearity), so they are independent:
`P(u ∉ covX) = (1-p)^{deg u}` and `k_u ~ Bin(deg u, p)`, whence
`E|covX| = Σ_u(1-(1-p)^{deg u})` and `E[S] = Σ_u E[k_u 1[k_u≥2]] = (1+O(ε))(θ-θe^{-θ})|V|`.
(3) For `v ∉ covX` all `D` edges through `v` are unkept, so
`deg_{𝓖'}(v) = #{e ∋ v : no kept edge meets e}` and each such event has probability
`(1-p)^{f(e)-deg v+1}` with `f(e) = Σ_{w∈e}(deg w-1) = #{f ≠ e : f ∩ e ≠ ∅}`; by linearity
the free blockers number `Σ_{w ∈ e∖{v}}(deg w - 1) ∈ ((r-1)(D-1))(1±O(ε))`, so the
conditional mean is `D'(1+O(ε(1+rθ)))`; the sum of `D` almost-independent indicators has
variance `≤ D'`, so any deviation target `≥ D'θ²` (in particular `ε'D' ≥ 100(ε+εrθ)D'`) is
reachable via the certificate for the blocked count `blk(v) = deg v - deg_{𝓖'}(v)` (`c = r`,
`s = 2(1+ε)D`) and `bj_talagrand`.
(4) `|X|`, `|covX|`, `S` concentrate around their means via `bj_talagrand` with certificates
`c = 1, s ≤ |𝓖|`; `c = r, s ≤ |V|`; and `c = 2r, s ≤ 2K|V|` with the exceptional outcome
`Ω* = {∃u : k_u > K}`, `K = log|V|`, `P(Ω*) ≤ |V|(eθ/K)^K ≤ |V|^{-2}`.
(5) Simultaneity: the symmetric Lovász Local Lemma (`lll_symmetric`, from
`Submission.Work.Deep.Reed.Prob.lll_symmetric`) applied to the per-vertex events (each
depends on the kept status of the edges meeting the edges through `v`, i.e. at most `rD²+1`
coordinates, and has probability `e^{-Ω(θ²D/ε'²)}`) together with the finitely many global
events (which depend on everything but have probability `e^{-Ω(θ²|V|)} ≤ e^{-Ω(θ²D)}`), the
LLL conditions `e·p·(d+1) ≤ 1` holding for `D ≥ Dmin`. -/
theorem nibble_round2 {r : ℕ} (hr : 2 ≤ r) {θ δ ε' ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100) (hδ0 : 0 < δ) (hδ1 : δ ≤ θ / 100)
    (hε'0 : 0 < ε') (hε'1 : ε' ≤ 1 / 2) (hε'2 : 100 * (ε + ε * (r : ℝ) * θ) ≤ ε')
    (hε0 : 0 < ε) (hε1 : ε ≤ θ / 100) (hεδ : 4 * ε ≤ δ) :
    ∃ Dmin : ℕ, 1 ≤ Dmin ∧ ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (𝓖 : Set (Set V)) (D : ℕ), Dmin ≤ D → D ≤ Fintype.card V →
      Work.Deep.Nibble.HLin 𝓖 → Work.Deep.Nibble.HUnif 𝓖 r →
      (∀ v : V, |((Work.Deep.Nibble.hd 𝓖 v : ℝ)) - (D : ℝ)| ≤ ε * (D : ℝ)) →
      ∃ ω : 𝓖 → Bool,
        Work.Deep.Nibble.RoundGood 𝓖 r D θ δ ε'
          ((D : ℝ) * (1 - θ / (D : ℝ)) ^ ((r - 1) * (D - 1))) ω := by
  obtain ⟨Dmin₀, hDmin₀1, hmain⟩ :=
    nibble_round2_asm hr hθ0 hθ1 hδ0 hδ1 hε'0 hε'1 hε'2 hε0 hε1 hεδ
  obtain ⟨N1, hN1⟩ := r2_num_basic hr hθ0 hθ1 hδ0 hδ1 hε'0 hε'1 hε'2 hε0 hε1 hεδ
  refine ⟨max Dmin₀ (N1 + 1), by omega, ?_⟩
  intro V _ _ 𝓖 D hDmin hDV hl hu hdeg
  have hDmin₀ : Dmin₀ ≤ D := le_trans (le_max_left _ _) hDmin
  have hN1le : N1 ≤ D := by
    have h : N1 + 1 ≤ D := le_trans (le_max_right _ _) hDmin
    omega
  obtain ⟨hD1, hthD, hD1ε, hθ2δ, -, -, -, -, -, -, -, -, h1e4, _⟩ := hN1 D hN1le
  have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD1
  have hD2 : 2 ≤ D := by
    have hle : (1-ε)*(D:ℝ) ≤ (D:ℝ) := by nlinarith [hε0, hDpos]
    have : (2:ℝ) ≤ (D:ℝ) := by linarith
    exact_mod_cast this
  have hD8 : 8 ≤ D := by
    have hδ : δ ≤ 1/10^4 := by linarith [hδ1, hθ1]
    have hδ2 : δ^2 ≤ 1/(10:ℝ)^8 := by nlinarith [hδ0, hδ]
    have hr2 : (2:ℝ)^2 ≤ (r:ℝ)^2 := by
      have : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
      nlinarith
    have h1 : (10:ℝ)^4 * (2:ℝ)^2 ≤ δ^2 * (D:ℝ) := by nlinarith [h1e4, hr2]
    have h3 : δ^2 * (D:ℝ) ≤ (1/(10:ℝ)^8) * (D:ℝ) :=
      mul_le_mul_of_nonneg_right hδ2 hDpos.le
    have : (8:ℝ) ≤ (D:ℝ) := by nlinarith only [h1, h3]
    exact_mod_cast this
  exact hmain 𝓖 D hDmin₀ hDV hl hu hdeg
    (fun hp0 hp1 v => r2_Wv_mean (δ := δ) 𝓖 hr hθ0 hθ1 hε'0 hε'1 hε'2 hD2 hp0 hp1 hthD hl hu hdeg v)
    (fun hp0 hp1 => r2_Y_mean 𝓖 hθ0 hθ1 hδ0 hε0 hεδ hD8 hp0 hp1 hthD hθ2δ hdeg)
    (fun hp0 hp1 => r2_S_mean 𝓖 hθ0 hθ1 hδ0 hδ1 hε0 hε1 hεδ hD8 hp0 hp1 hthD hθ2δ hdeg)

end Work.Deep.Nibble
