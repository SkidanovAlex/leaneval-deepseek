import Mathlib
import Submission.Work.LT.Defs
import Submission.Work.LT.tensorCode_finrank_ge
import Submission.Work.LT.cover_le_lrCode
import Submission.Work.LT.finrank_inf_comap_le

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/LT/DESIGN.md first (the orchestrator's design; your lemma is one node of its DAG). Shared definitions: Submission/Work/LT/Defs.lean (namespace Work.LT) — do NOT edit it; if you need a new shared definition, put it in your own file. Siblings are being proved in parallel; import them when they land.

# lr_rate — guidance

**Idea.** Rate via the vertex cover `V00 ∪ V11` (DELLM Lem 4.3, bipartite case `ν = 1/2`).

1. **Implied constraints.** If the views at all type-00 and type-11 vertices lie in `CA ⊗ CB`
   then so do the views at type 10 and 01. So
   `lrCode = ⨅ g, (T.comap (lrView 0 0 g)) ⊓ (T.comap (lrView 1 1 g))`, `T = tensorCode CA CB`.
2. **Tensor dimension.** `finrank T ≥ kA * kB`.
3. **Counting.** `codim (⨅ over ≤ 2|G| maps) ≤ Σ codim`.
4. `dim ≥ |G|Δ² - 2|G|(Δ² - kA kB) ≥ |G|Δ²(1 - 2(1 - r0²))`, using `kA kB ≥ r0² Δ²`.

The three steps 1-3 are carried out in the imported files `cover_le_lrCode.lean`,
`tensorCode_finrank_ge.lean` (step 2) and `finrank_inf_comap_le.lean` (step 3, in the general form
"the intersection of the `2|ι|` preimages of `T` has codimension at most `2|ι| codim T`").
This file assembles them and does the arithmetic of step 4.
-/

namespace Work.LT

open Classical

/-- Membership in `tensorCode CA CB`, unfolded: every row (fixed first index) lies in `CB` and
every column (fixed second index) lies in `CA`. -/
private lemma mem_tensorCode_iff {Δ : ℕ} {CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)}
    {w : Fin Δ × Fin Δ → ZMod 2} :
    w ∈ tensorCode CA CB ↔ (∀ i, (fun j => w (i, j)) ∈ CB) ∧ (∀ j, (fun i => w (i, j)) ∈ CA) := by
  have h1 : ∀ i : Fin Δ, (LinearMap.funLeft (ZMod 2) (ZMod 2) (fun j : Fin Δ => (i, j))) w
      = (fun j => w (i, j)) := by
    intro i; funext j; rw [LinearMap.funLeft_apply]
  have h2 : ∀ j : Fin Δ, (LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin Δ => (i, j))) w
      = (fun i => w (i, j)) := by
    intro j; funext i; rw [LinearMap.funLeft_apply]
  simp [tensorCode, Submodule.mem_comap, h1, h2]

/-- **Rate** (DELLM Lem 4.3, bipartite vertex cover). The type-00 and type-11 vertices cover
every edge, so the code is cut out by `2|G|` copies of the tensor constraints, each of
codimension `≤ Δ² - dim CA · dim CB`. Hence `dim ≥ (2 r0² - 1) |G| Δ²`. -/
theorem lr_rate {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) (r0 : ℝ) (hr0 : 0 ≤ r0)
    (hA : r0 * Δ ≤ Module.finrank (ZMod 2) CA) (hB : r0 * Δ ≤ Module.finrank (ZMod 2) CB) :
    (2 * r0 ^ 2 - 1) * (Fintype.card G * Δ * Δ) ≤
      Module.finrank (ZMod 2) (lrCode A B CA CB) := by
  classical
  -- Abbreviations: `T` is the tensor code, `P`/`Q` the type-00 and type-11 constraint families.
  set T : Submodule (ZMod 2) (Fin Δ × Fin Δ → ZMod 2) := tensorCode CA CB with hT
  set P : Submodule (ZMod 2) (G × Fin Δ × Fin Δ → ZMod 2) :=
    ((⨅ g : G, T.comap (lrView A B 0 0 g)) :
      Submodule (ZMod 2) (G × Fin Δ × Fin Δ → ZMod 2)) with hP
  set Q : Submodule (ZMod 2) (G × Fin Δ × Fin Δ → ZMod 2) :=
    ((⨅ g : G, T.comap (lrView A B 1 1 g)) :
      Submodule (ZMod 2) (G × Fin Δ × Fin Δ → ZMod 2)) with hQ
  -- Step 1: the type-00 and type-11 constraints imply all the constraints.
  have hcover : P ⊓ Q ≤ lrCode A B CA CB := by
    rw [hP, hQ, hT]
    exact cover_le_lrCode A B CA CB
  have hle : Module.finrank (ZMod 2) ((P ⊓ Q :
      Submodule (ZMod 2) (G × Fin Δ × Fin Δ → ZMod 2))) ≤
      Module.finrank (ZMod 2) (lrCode A B CA CB) :=
    Submodule.finrank_mono hcover
  -- Step 3: counting codimensions of the two `|G|`-indexed families of constraints.
  have hcount : Module.finrank (ZMod 2) (G × Fin Δ × Fin Δ → ZMod 2) ≤
      Module.finrank (ZMod 2) ((P ⊓ Q :
        Submodule (ZMod 2) (G × Fin Δ × Fin Δ → ZMod 2))) +
        (Fintype.card G + Fintype.card G) *
          Module.finrank (ZMod 2) ((Fin Δ × Fin Δ → ZMod 2) ⧸ T) := by
    rw [hP, hQ, hT]
    exact finrank_inf_comap_le (fun g : G => lrView A B 0 0 g)
      (fun g : G => lrView A B 1 1 g) T
  -- Dimensions.
  have hV : Module.finrank (ZMod 2) (G × Fin Δ × Fin Δ → ZMod 2) = Fintype.card G * Δ * Δ := by
    rw [Module.finrank_pi, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
    ring
  have hqT : Module.finrank (ZMod 2) ((Fin Δ × Fin Δ → ZMod 2) ⧸ T) +
      Module.finrank (ZMod 2) T = Δ * Δ := by
    rw [Submodule.finrank_quotient_add_finrank, Module.finrank_pi, Fintype.card_prod,
      Fintype.card_fin]
  have hTge : Module.finrank (ZMod 2) CA * Module.finrank (ZMod 2) CB ≤
      Module.finrank (ZMod 2) T := by
    rw [hT]
    exact tensorCode_finrank_ge CA CB
  -- Step 4a: `finrank lrCode ≥ |G| Δ² - 2 |G| (Δ² - dim T)`, in `ℝ`.
  have hreal : (Fintype.card G : ℝ) * (Δ : ℝ) * (Δ : ℝ) -
      2 * (Fintype.card G : ℝ) * ((Δ : ℝ) * (Δ : ℝ) - (Module.finrank (ZMod 2) T : ℝ)) ≤
      (Module.finrank (ZMod 2) (lrCode A B CA CB) : ℝ) := by
    have hnat : Fintype.card G * Δ * Δ ≤
        Module.finrank (ZMod 2) (lrCode A B CA CB) +
          (Fintype.card G + Fintype.card G) *
            Module.finrank (ZMod 2) ((Fin Δ × Fin Δ → ZMod 2) ⧸ T) := by
      rw [← hV]
      exact le_trans hcount (Nat.add_le_add_right hle _)
    have h1 : ((Fintype.card G * Δ * Δ : ℕ) : ℝ) ≤
        (Module.finrank (ZMod 2) (lrCode A B CA CB) : ℝ) +
          (((Fintype.card G + Fintype.card G) *
            Module.finrank (ZMod 2) ((Fin Δ × Fin Δ → ZMod 2) ⧸ T) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hqcast : ((Module.finrank (ZMod 2) ((Fin Δ × Fin Δ → ZMod 2) ⧸ T) : ℕ) : ℝ)
        = (Δ : ℝ) * (Δ : ℝ) - (Module.finrank (ZMod 2) T : ℝ) := by
      have hc := congrArg (fun m : ℕ => (m : ℝ)) hqT
      push_cast at hc
      linarith
    push_cast at h1
    rw [hqcast] at h1
    linarith
  -- Step 4b: `dim T ≥ r0² Δ²`.
  have htR : r0 ^ 2 * ((Δ : ℝ) * (Δ : ℝ)) ≤ (Module.finrank (ZMod 2) T : ℝ) := by
    have hTge' : ((Module.finrank (ZMod 2) CA : ℝ)) * (Module.finrank (ZMod 2) CB : ℝ)
        ≤ (Module.finrank (ZMod 2) T : ℝ) := by exact_mod_cast hTge
    have hsq : (r0 * (Δ : ℝ)) * (r0 * (Δ : ℝ)) ≤
        (Module.finrank (ZMod 2) CA : ℝ) * (Module.finrank (ZMod 2) CB : ℝ) := by
      have h0 : (0 : ℝ) ≤ r0 * (Δ : ℝ) := mul_nonneg hr0 (Nat.cast_nonneg _)
      exact mul_le_mul hA hB h0 (le_trans h0 hA)
    nlinarith [hsq, hTge']
  -- Step 4c: final arithmetic.
  have hG : (0 : ℝ) ≤ (Fintype.card G : ℝ) := Nat.cast_nonneg _
  nlinarith [hreal, htR, hG]

end Work.LT
