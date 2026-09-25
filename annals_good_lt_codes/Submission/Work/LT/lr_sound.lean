import Mathlib
import Submission.Work.LT.Defs
import Submission.Work.LT.lr_sound_defs
import Submission.Work.LT.lr_local_opt_far
import Submission.Work.LT.dispCount_lrW0_le
import Submission.Work.LT.local_search
import Submission.Work.LT.hammingDist_lrState_le

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/LT/DESIGN.md first (the orchestrator's design; your lemma is one node of its DAG). Shared definitions: Submission/Work/LT/Defs.lean (namespace Work.LT) — do NOT edit it; if you need a new shared definition, put it in your own file. Siblings are being proved in parallel; import them when they land.

# lr_sound — guidance

DELLM Thm 4.5 = Propositions 4.7 + 4.8 (§4.2), quadripartite form, using `lr_local_opt_far`.
Write `V0` = set of rejecting vertices (`lrView … f ∉ T`), `ζ = |V0|/(4|G|)`, `c = κ0δ0/(8+κ0)`.

1. If `c - μ ≤ 0`, take `c := 0`: the LHS is `≤ 0`. Assume `c > μ`; note `c - μ ≤ c < δ0 ≤ 1`.
2. `W0 α β g` := a nearest element of `T = CA ⊗ CB` to the view of `f` (exists: `T` finite,
   nonempty; `Finset.exists_min_image`). Non-rejecting vertices have `W0 = view`.
   `dispCount W0 ≤ 2Δ |V0|` (every disputed edge has a rejecting endpoint).
3. **Local search as well-founded induction** (no algorithm needed): prove
   `∀ N, ∀ W valid, dispCount W ≤ N → ∃ W' valid, IsLocalOpt W' ∧
   #{v | W' v ≠ W v} ≤ dispCount W - dispCount W'` by induction on `N` (if `W` is not locally
   optimal, one single-vertex change strictly decreases `dispCount`). Apply to `W0`: final `W`,
   changed set `V1`, `|V1| ≤ 2Δ|V0|`.
4. By `lr_local_opt_far`: either `dispCount W = 0` or `(c-μ)|G| ≤ dispCount W ≤ 2Δ|V0|`.
   * **Far case:** `ζ ≥ (c-μ)/(8Δ) ≥ κ`, and `dist/n ≤ 1`; take any codeword (e.g. `0`).
   * **Zero case:** define `f0 (x,i,j) := W 0 0 x (i,j)`. No disputes ⇒ the four vertices of every
     square agree (chain 00—10 A-edge, 00—01 B-edge, 01—11 A-edge), so every view of `f0` equals
     the corresponding `W` entry, so `f0 ∈ lrCode`. Squares away from `V0 ∪ V1` have
     `f0 = f`. Each vertex touches `Δ²` squares: `dist(f,f0) ≤ Δ²(1+2Δ)|V0|`, i.e.
     `dist/(|G|Δ²) ≤ 4(1+2Δ) ζ`, and `κ ≤ 1/(16(Δ+1)) ≤ 1/(4(1+2Δ))`.
5. `κ = (c-μ)/(16(Δ+1))` is below both `1/(4(1+2Δ))` and `(c-μ)/(8Δ)`.

Expected size: 600–1000 lines.
-/

namespace Work.LT

open Classical

/-- **Local testability** (DELLM Thm 4.5, quadripartite form). The test "pick one of the
`4|G|` vertices uniformly and check its local view lies in `CA ⊗ CB`" rejects every word `f`
with probability at least `κ · dist(f, C)/|G|Δ²`, `κ = (c - μ) / (16 (Δ + 1))`,
`c = κ0 δ0 / (8 + κ0)`. -/
theorem lr_sound {G : Type} [Group G] [Fintype G] {Δ : ℕ} (hΔ : 0 < Δ) (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) (δ0 κ0 μ : ℝ) (hκ0 : 0 < κ0)
    (hδ1 : δ0 ≤ 1) (hμ : 0 ≤ μ)
    (hdA : ∀ x ∈ CA, x ≠ 0 → δ0 * Δ ≤ hammingNorm x)
    (hdB : ∀ x ∈ CB, x ≠ 0 → δ0 * Δ ≤ hammingNorm x)
    (hagr : agreementTestable κ0 CA CB) (hA : leftExpander A μ) (hB : rightExpander B μ)
    (f : G × Fin Δ × Fin Δ → ZMod 2) :
    ∃ c ∈ lrCode A B CA CB,
      (κ0 * δ0 / (8 + κ0) - μ) / (16 * (Δ + 1)) *
          ((hammingDist f c : ℝ) / (Fintype.card G * Δ * Δ)) ≤
        ((Finset.univ.filter (fun v : Fin 2 × Fin 2 × G =>
            lrView A B v.1 v.2.1 v.2.2 f ∉ tensorCode CA CB)).card : ℝ) /
          (4 * Fintype.card G) := by
  classical
  have hV0 : (Finset.univ.filter (fun v : Fin 2 × Fin 2 × G =>
      lrView A B v.1 v.2.1 v.2.2 f ∉ tensorCode CA CB)) = rejectSet A B CA CB f := rfl
  rw [hV0]
  have hDpos : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast hΔ
  have hNpos : (0 : ℝ) < (Fintype.card G : ℝ) := by
    have : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨1⟩
    exact_mod_cast this
  have hNnonneg : (0 : ℝ) ≤ (Fintype.card G : ℝ) := hNpos.le
  have hNDDpos : (0 : ℝ) < (Fintype.card G : ℝ) * (Δ : ℝ) * (Δ : ℝ) :=
    mul_pos (mul_pos hNpos hDpos) hDpos
  rcases le_or_gt (κ0 * δ0 / (8 + κ0) - μ) 0 with hnonpos | hpos
  · -- κ ≤ 0 : the zero codeword already witnesses the (vacuous) inequality
    refine ⟨0, zero_mem _, ?_⟩
    have hκ : (κ0 * δ0 / (8 + κ0) - μ) / (16 * ((Δ : ℝ) + 1)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hnonpos (by positivity)
    have hX : (0 : ℝ) ≤ (hammingDist f (0 : G × Fin Δ × Fin Δ → ZMod 2) : ℝ) /
        ((Fintype.card G : ℝ) * (Δ : ℝ) * (Δ : ℝ)) :=
      div_nonneg (Nat.cast_nonneg _) hNDDpos.le
    have hR : (0 : ℝ) ≤ ((rejectSet A B CA CB f).card : ℝ) / (4 * (Fintype.card G : ℝ)) :=
      div_nonneg (Nat.cast_nonneg _) (by positivity)
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hκ hX) hR
  · -- main case: κ0 δ0 / (8 + κ0) - μ > 0
    have hcpos : (0 : ℝ) < κ0 * δ0 / (8 + κ0) := by linarith
    have hδ0pos : (0 : ℝ) < δ0 := by
      by_contra h
      have hle : δ0 ≤ 0 := le_of_not_gt h
      have h8 : (0 : ℝ) < 8 + κ0 := by linarith
      have : κ0 * δ0 / (8 + κ0) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by nlinarith) h8.le
      linarith
    have hc_le_one : κ0 * δ0 / (8 + κ0) - μ ≤ 1 := by
      have hle : κ0 * δ0 / (8 + κ0) ≤ δ0 := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 8 + κ0)]
        nlinarith
      linarith
    have hκle : (κ0 * δ0 / (8 + κ0) - μ) / (16 * ((Δ : ℝ) + 1)) ≤
        1 / (4 * (1 + 2 * (Δ : ℝ))) := by
      have h1 : (κ0 * δ0 / (8 + κ0) - μ) / (16 * ((Δ : ℝ) + 1)) ≤
          1 / (16 * ((Δ : ℝ) + 1)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      have h2 : 1 / (16 * ((Δ : ℝ) + 1)) ≤ 1 / (4 * (1 + 2 * (Δ : ℝ))) := by
        apply one_div_le_one_div_of_le (by positivity)
        linarith
      linarith
    have hκnonneg : (0 : ℝ) ≤ (κ0 * δ0 / (8 + κ0) - μ) / (16 * ((Δ : ℝ) + 1)) :=
      div_nonneg hpos.le (by positivity)
    -- the initial assignment and the local search
    obtain ⟨W, hWmem, hWopt, hWch, hWleW0⟩ :=
      local_search A B CA CB (lrW0 A B CA CB f) (fun α β g => lrW0_mem A B CA CB f α β g)
        (lrW0 A B CA CB f) (fun α β g => lrW0_mem A B CA CB f α β g)
        (by simp [changedSet]) le_rfl
    have hW0le : dispCount A B (lrW0 A B CA CB f) ≤ 2 * Δ * (rejectSet A B CA CB f).card :=
      dispCount_lrW0_le A B CA CB f
    have hWle : dispCount A B W ≤ 2 * Δ * (rejectSet A B CA CB f).card :=
      le_trans hWleW0 hW0le
    have hMnonneg : (0 : ℝ) ≤ ((rejectSet A B CA CB f).card : ℝ) := Nat.cast_nonneg _
    rcases lr_local_opt_far A B CA CB δ0 κ0 μ hκ0 hδ1 hμ hdA hdB hagr hA hB W hWmem hWopt with
      hzero | hfar
    · -- dispCount W = 0 : read off the type-(0,0) vertices
      have hV1le : (changedSet W (lrW0 A B CA CB f)).card ≤
          2 * Δ * (rejectSet A B CA CB f).card :=
        le_trans hWch (le_trans (Nat.sub_le _ _) hW0le)
      have hdist : hammingDist f (lrState W) ≤
          Δ * Δ * ((rejectSet A B CA CB f).card + (changedSet W (lrW0 A B CA CB f)).card) :=
        hammingDist_lrState_le A B CA CB f W (changedSet W (lrW0 A B CA CB f)) (by
          intro v hv hv1
          have h1 : W v.1 v.2.1 v.2.2 = lrW0 A B CA CB f v.1 v.2.1 v.2.2 := by
            by_contra hc
            exact hv1 (by simp [changedSet, hc])
          rw [h1]
          exact lrW0_eq_view_of_not_mem_rejectSet A B CA CB f v hv)
      have hmem : lrState W ∈ lrCode A B CA CB := lrState_mem_lrCode hWmem hzero
      refine ⟨lrState W, hmem, ?_⟩
      have hdistR : (hammingDist f (lrState W) : ℝ) ≤ (Δ : ℝ) * (Δ : ℝ) *
          (((rejectSet A B CA CB f).card : ℝ) + ((changedSet W (lrW0 A B CA CB f)).card : ℝ)) := by
        have h := Nat.cast_le (α := ℝ).mpr hdist
        push_cast at h
        linarith
      have hV1R : ((changedSet W (lrW0 A B CA CB f)).card : ℝ) ≤
          2 * (Δ : ℝ) * ((rejectSet A B CA CB f).card : ℝ) := by
        have h := Nat.cast_le (α := ℝ).mpr hV1le
        push_cast at h
        linarith
      have hfrac1 : (hammingDist f (lrState W) : ℝ) /
          ((Fintype.card G : ℝ) * (Δ : ℝ) * (Δ : ℝ)) ≤
          (((rejectSet A B CA CB f).card : ℝ) + ((changedSet W (lrW0 A B CA CB f)).card : ℝ)) /
            (Fintype.card G : ℝ) := by
        rw [div_le_div_iff₀ hNDDpos hNpos]
        nlinarith [hdistR, hNpos]
      have hfrac2 : (((rejectSet A B CA CB f).card : ℝ) +
            ((changedSet W (lrW0 A B CA CB f)).card : ℝ)) / (Fintype.card G : ℝ) ≤
          4 * (1 + 2 * (Δ : ℝ)) *
            (((rejectSet A B CA CB f).card : ℝ) / (4 * (Fintype.card G : ℝ))) := by
        rw [← mul_div_assoc]
        have h4 : 4 * (1 + 2 * (Δ : ℝ)) * ((rejectSet A B CA CB f).card : ℝ) =
            ((1 + 2 * (Δ : ℝ)) * ((rejectSet A B CA CB f).card : ℝ)) * 4 := by ring
        have hN4 : 4 * (Fintype.card G : ℝ) = (Fintype.card G : ℝ) * 4 := by ring
        rw [h4, hN4, mul_div_mul_right _ _ (by norm_num : (4:ℝ) ≠ 0)]
        rw [div_le_div_iff₀ hNpos hNpos]
        nlinarith [hV1R, hNpos]
      calc
        (κ0 * δ0 / (8 + κ0) - μ) / (16 * ((Δ : ℝ) + 1)) *
            ((hammingDist f (lrState W) : ℝ) / ((Fintype.card G : ℝ) * (Δ : ℝ) * (Δ : ℝ)))
            ≤ (1 / (4 * (1 + 2 * (Δ : ℝ)))) * (4 * (1 + 2 * (Δ : ℝ)) *
                (((rejectSet A B CA CB f).card : ℝ) / (4 * (Fintype.card G : ℝ)))) :=
              mul_le_mul hκle (le_trans hfrac1 hfrac2)
                (div_nonneg (Nat.cast_nonneg _) hNDDpos.le) (by positivity)
        _ = ((rejectSet A B CA CB f).card : ℝ) / (4 * (Fintype.card G : ℝ)) := by
              rw [one_div, inv_mul_cancel_left₀ (by positivity : (4:ℝ) * (1 + 2 * (Δ : ℝ)) ≠ 0)]
    · -- dispCount W ≥ (c - μ)|G| : the rejecting vertices are already many
      have hcast : (dispCount A B W : ℝ) ≤ 2 * (Δ : ℝ) * ((rejectSet A B CA CB f).card : ℝ) := by
        have h := Nat.cast_le (α := ℝ).mpr hWle
        push_cast at h
        linarith
      have hζ : (κ0 * δ0 / (8 + κ0) - μ) / (16 * ((Δ : ℝ) + 1)) ≤
          ((rejectSet A B CA CB f).card : ℝ) / (4 * (Fintype.card G : ℝ)) := by
        have h1 : (κ0 * δ0 / (8 + κ0) - μ) / (16 * ((Δ : ℝ) + 1)) ≤
            (κ0 * δ0 / (8 + κ0) - μ) / (8 * (Δ : ℝ)) := by
          apply div_le_div_of_nonneg_left hpos.le (by linarith)
          linarith
        have h2 : (κ0 * δ0 / (8 + κ0) - μ) / (8 * (Δ : ℝ)) ≤
            ((rejectSet A B CA CB f).card : ℝ) / (4 * (Fintype.card G : ℝ)) := by
          rw [div_le_div_iff₀ (by linarith) (by positivity)]
          nlinarith [hfar, hcast, hNpos, hDpos]
        linarith
      refine ⟨0, zero_mem _, ?_⟩
      have hdist1 : (hammingDist f (0 : G × Fin Δ × Fin Δ → ZMod 2) : ℝ) /
          ((Fintype.card G : ℝ) * (Δ : ℝ) * (Δ : ℝ)) ≤ 1 := by
        rw [div_le_one hNDDpos]
        have hcard : hammingDist f (0 : G × Fin Δ × Fin Δ → ZMod 2) ≤
            Fintype.card G * Δ * Δ := by
          have h1 : hammingDist f (0 : G × Fin Δ × Fin Δ → ZMod 2) ≤
              Fintype.card (G × Fin Δ × Fin Δ) := by
            rw [hammingDist]
            simpa using Finset.card_filter_le (Finset.univ : Finset (G × Fin Δ × Fin Δ))
              (fun p => f p ≠ 0)
          have h2 : Fintype.card (G × Fin Δ × Fin Δ) = Fintype.card G * Δ * Δ := by
            simp [Fintype.card_prod, Nat.mul_assoc]
          linarith
        have h := Nat.cast_le (α := ℝ).mpr hcard
        push_cast at h
        linarith
      calc
        (κ0 * δ0 / (8 + κ0) - μ) / (16 * ((Δ : ℝ) + 1)) *
            ((hammingDist f (0 : G × Fin Δ × Fin Δ → ZMod 2) : ℝ) /
              ((Fintype.card G : ℝ) * (Δ : ℝ) * (Δ : ℝ)))
            ≤ (κ0 * δ0 / (8 + κ0) - μ) / (16 * ((Δ : ℝ) + 1)) * 1 :=
              mul_le_mul_of_nonneg_left hdist1 hκnonneg
        _ = (κ0 * δ0 / (8 + κ0) - μ) / (16 * ((Δ : ℝ) + 1)) := mul_one _
        _ ≤ ((rejectSet A B CA CB f).card : ℝ) / (4 * (Fintype.card G : ℝ)) := hζ

end Work.LT
