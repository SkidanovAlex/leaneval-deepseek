/-
  WilG4c / FibDiscMain / `fibDisc_mem_uniform` — the fibre-wise discontinuity locus of an
  `Ω`-definable function is `Ω`-definable, with format and degree *uniform* in the degree
  parameter `D`.

  The construction and all its vocabulary live in `FibDiscAux`; the two quantifier-plumbing
  lemmas (`fibResMemGeneric`: the set identity of the `∃ε>0 ∀δ>0` chain; `fibResChainMem`: the
  `Ω`-bookkeeping of that chain) and the uniform `Ω`-membership of the body (`bodyA_mem_uniform`)
  are separate modules.  Here we

  * identify `resA H` with the fibre-wise discontinuity locus `fibDisc H` (`resA_eq_fibDisc`,
    using the `ε`-`δ` form of discontinuity of `Work.WilG1.Cell.Junk.not_continuousAt_aux` and
    the splitting `w = (w_l, w_z)` reassembled, `append_split`);
  * collect the `Ω`-membership with uniform format and degree (`resA_mem_uniform`);
  * raise the format to the requested `F + K`.
-/
import Mathlib
import Submission.Work.WilG4c.FibreCoreDefs
import Submission.Work.WilG1.Cell.Junk.DiscDefs
import Submission.Work.WilG1.Cell.Junk.disc_mem
import Submission.Work.WilG4c.FibDiscMain.FibDiscAux
import Submission.Work.WilG4c.FibDiscMain.fibResChainMem
import Submission.Work.WilG4c.FibDiscMain.bodyA_mem_uniform

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
open scoped BigOperators

open WilkiesDesign

namespace Work.WilG4c.FibDiscMain

/-! ## 1. Unfolding the `ε`-`δ` description -/

/-- The quantifier chain `∃ε>0 ∀δ>0` built from projections and complements: for an arbitrary
"body" `B` of parameters `(w, ε, δ) ∈ ℝ^{n+2}`, the set `projN 1 (posESet n ∩ (projN 1 (posDSet n
∩ Bᶜ))ᶜ)` is the set of `w` such that some `ε > 0` is realised for every `δ > 0` with
`(w,ε,δ) ∈ B`. -/
theorem fibResMem (n : ℕ) (B : Set (Fin (n + 2) → ℝ)) :
    Work.WilG5.projN 1 (Work.WilG1.Cell.Junk.posESet n ∩
        (Work.WilG5.projN 1 (Work.WilG1.Cell.Junk.posDSet n ∩ Bᶜ))ᶜ)
      = {w : Fin n → ℝ | ∃ ε > 0, ∀ δ > 0,
          Fin.append (Fin.append w (fun _ : Fin 1 => ε)) (fun _ : Fin 1 => δ) ∈ B} := by
  ext w
  rw [Work.WilG5.projN, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e, he⟩
    rw [Set.mem_inter_iff] at he
    obtain ⟨he1, he2⟩ := he
    rw [Work.WilG1.Cell.Junk.mem_posESet_append] at he1
    rw [Set.mem_compl_iff, Work.WilG5.projN, Set.mem_ofPred_eq, not_exists] at he2
    have key : ∀ d : Fin 1 → ℝ, 0 < d 0 → Fin.append (Fin.append w e) d ∈ B := by
      intro d hd
      by_contra hc
      exact he2 d ⟨by rw [Work.WilG1.Cell.Junk.posDSet, Set.mem_ofPred_eq,
            Work.WilG1.Cell.Junk.appAA_dIdxA]; exact hd,
          by rwa [Set.mem_compl_iff]⟩
    refine ⟨e 0, he1, fun δ hδ => ?_⟩
    have h := key (fun _ : Fin 1 => δ) (by simpa using hδ)
    rwa [Work.WilG1.Cell.Junk.fin1_ext e] at h
  · rintro ⟨ε, hε, h⟩
    refine ⟨fun _ : Fin 1 => ε, ?_, ?_⟩
    · rw [Work.WilG1.Cell.Junk.mem_posESet_append]
      simpa using hε
    · rw [Set.mem_compl_iff, Work.WilG5.projN, Set.mem_ofPred_eq, not_exists]
      intro d hd
      rw [Set.mem_inter_iff] at hd
      obtain ⟨hd1, hd2⟩ := hd
      rw [Work.WilG1.Cell.Junk.posDSet, Set.mem_ofPred_eq,
        Work.WilG1.Cell.Junk.appAA_dIdxA] at hd1
      rw [Set.mem_compl_iff] at hd2
      have hmem : Fin.append (Fin.append w (fun _ : Fin 1 => ε)) (fun _ : Fin 1 => d 0) ∈ B :=
        h (d 0) hd1
      rw [← Work.WilG1.Cell.Junk.fin1_ext d] at hmem
      exact hd2 hmem

/-- The meaning of `resA`: `w` lies in it iff the fibre function `z ↦ H(w_l, z)` has an
oscillation `ε > 0` at `w_z` on every scale `δ > 0`. -/
theorem mem_resA {p N : ℕ} {H : (Fin (p + N) → ℝ) → ℝ} {w : Fin (p + N) → ℝ} :
    w ∈ resA p N H ↔ ∃ ε > 0, ∀ δ > 0, ∃ z' : Fin N → ℝ,
      (∑ j : Fin N, (z' j - w (Fin.natAdd p j)) ^ 2) < δ ^ 2 ∧
      ε ^ 2 ≤ (H (Fin.append (fun i : Fin p => w (Fin.castAdd N i)) z') - H w) ^ 2 := by
  have hgen := fibResMem (p + N) (bodyA p N H)
  simp only [resA, resBA, forallDA, existDA]
  rw [hgen, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε, hε, fun δ hδ => ?_⟩
    have hb := (mem_bodyA (p := p) (N := N) (H := H) (u := mkMid p N w ε δ)).mp
      (h δ hδ)
    simpa only [appAA_bPar, appAA_bFib, appAA_bEps, appAA_bDel, bAll_appendAA] using hb
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε, hε, fun δ hδ => ?_⟩
    rw [mem_bodyA]
    obtain ⟨z', hz1, hz2⟩ := h δ hδ
    exact ⟨z', by simpa only [appAA_bFib, appAA_bDel] using hz1,
      by simpa only [appAA_bPar, appAA_bEps, bAll_appendAA] using hz2⟩

/-- **The set identity:** the `ε`-`δ` description `resA` is the fibre-wise discontinuity locus
`fibDisc` (the parameter coordinates are held fixed inside the witness quantifier). -/
theorem resA_eq_fibDisc (p N : ℕ) (H : (Fin (p + N) → ℝ) → ℝ) :
    resA p N H = Work.WilG4c.fibDisc H := by
  ext w
  rw [mem_resA, Work.WilG4c.fibDisc, Set.mem_ofPred_eq,
    Work.WilG1.Cell.Junk.not_continuousAt_aux]
  simp only [append_split]

/-! ## 2. Uniform `Ω`-membership -/

/-- `resA H` is `Ω`-definable with a format and a degree polynomial independent of the degree
parameter `D` and of `H`. -/
theorem resA_mem_uniform (S : WilkiesDesign.SOMin) (p N F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (H : (Fin (p + N) → ℝ) → ℝ),
      WilkiesDesign.graphOf H ∈ S.Ω F D (p + N + 1) →
      resA p N H ∈ S.Ω a (b.eval D) (p + N) := by
  obtain ⟨a₀, b₀, hbody⟩ := bodyA_mem_uniform S p N F
  obtain ⟨A, B, hchain⟩ := fibResChainMem S (p + N)
  refine ⟨a₀ + A, b₀ + B, fun D H hH => ?_⟩
  have hb : bodyA p N H ∈ S.Ω a₀ (b₀.eval D) (p + N + 2) := hbody D H hH
  have h := hchain D (bodyA p N H) a₀ b₀ hb
  simpa only [resA, resBA, forallDA, existDA] using h

/-! ## 3. The requested statement -/

theorem fibDisc_mem_uniform (S : WilkiesDesign.SOMin) (p N F : ℕ) :
    ∃ (K : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (H : (Fin (p + N) → ℝ) → ℝ),
      WilkiesDesign.graphOf H ∈ S.Ω F D (p + N + 1) →
      Work.WilG4c.fibDisc H ∈ S.Ω (F + K) (b.eval D) (p + N) := by
  obtain ⟨a, b, hA⟩ := resA_mem_uniform S p N F
  refine ⟨a, b, fun D H hH => ?_⟩
  rw [← resA_eq_fibDisc p N H]
  exact Work.WilG1.Omega.mono (hA D H hH) (Nat.le_add_left a F) le_rfl

end Work.WilG4c.FibDiscMain
