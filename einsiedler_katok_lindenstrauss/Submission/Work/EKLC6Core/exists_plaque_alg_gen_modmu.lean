import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.countableGenEntropy
import Submission.Work.EKLC6Core.HcondSig_iInf
import Submission.Work.EKLC6Core.plaquePartitionAux
import Submission.Work.EKLC6Core.cellW_margin_exists_sep
import Submission.Work.EKLC6Core.desc_plaque_algebra_conull_ergodic_gen
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.uniform_contraction_horo
import Submission.Work.EKLC6Core.atom_iSup_comap_iterate_eq
import Submission.Work.EKLC6Core.GeneratesModMuSet_of_atom_singleton
import Submission.Work.EKLC6Geo.gen_plaque_erg_copy
import Submission.Work.EKLComp.X3Background
import Submission.Work.EKLC6Core.C6_tsum_entropy
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Route.exists_chart
import Submission.Work.EKLC6Route.exists_window
import Submission.Work.EKLC6Route.S_basic
import Submission.Work.EKLC6Route.plaque_data
import Submission.Work.EKLC6Route.ae_frequently_mem_neg
import Submission.Work.EKLC6Route.tsum_negMulLog_ne_top

/-!
# `Work.EKLC6Core.exists_plaque_alg_gen_modmu` — the mod-`μ` countable generator (Pisa 7.43)

**The target** (frozen): for a probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` preserved by and ergodic
for `φ = (aDiag t ·)`, with `Uminus t ≠ ⊥`, there are a countable Borel family `S` and a
`μ`-conull `Z` with

* `⨆_n comap (φ^[n]) σ(S)` a plaque algebra for `Uminus t` on `Z` (Pisa Def. 6.2),
* `GeneratesModMuSet μ t S` (Pisa 7.43: `S` generates the Borel σ-algebra modulo `μ`), and
* `HcondSig μ (σ (range S)) ⊥ ≠ ⊤` (Pisa 7.50/7.52: finite static entropy).

## Diagnosis of the remaining input (this session)

The whole content is Pisa's generator construction §7.47–7.53.  Writing `A_p := ⨆_n comap (φ^[n]) σ(S)`
for the past σ-algebra of `S`, the three clauses are *independent* in structure and only the third
is missing from the tree:

* **(clause 1, available).**  `Work.EKLC6Geo.cellW_uniform_margin` (and its
  `EKLC6Core` counterpart) produce a *countably generated* σ-algebra `A`, a conull `Z` and a
  **uniform** entrywise bound `C`, with `IsPlaqueAlgebra (Uminus t) Z A` and `comap φ A ≤ A`.
  Hence, for `S` a countable family with `σ (range S) = A`, one has `A_p = A` (the `n = 0` term
  already gives `A ⊇ A_p`, the decrease of `A` gives `A_p ⊆ A`) — clause 1 for free.
* **(clause 2, proved below, `exists_plaque_alg_gen_modmu_of_coarse`).**  The *modulo-`μ`*
  generation clause does **not** need the singleton refinement `exists_refine_singletons_g`
  (that refinement makes atoms singletons off `Z`, which is what makes the exact equality
  `⨆_n comap (ψ^[n]) A = borel X₃` true, but costs an infinite static entropy: it contains a
  countable *base* of the topology of `Zᶜ`).  Modulo `μ` it suffices that the backward orbit of
  `μ`-a.e. `x` stays in `Z`: on that set the atoms of `J = ⨆_n comap (ψ^[n]) A` are singletons
  (`iSup_comap_neg_atom_singleton_ae` below: `y ∈ [x]_J` gives `ψ^n y = u_n • ψ^n x` with `u_n`
  in the (uniformly bounded!) `A`-shape, whence `y = (a^n u_n a^{-n}) • x` with the conjugates
  `→ 1` by `uniform_contraction_horo`, so `y = x`), and the exceptional set
  `⋃_n ψ^{-n}(Zᶜ)` is `μ`-null.  `generatesModMuSet_of_atom_singleton` then gives clause 2.
* **(clause 3, OPEN — the genuinely missing geometric input).**  The *only* remaining obligation
  is finite static entropy of a past-plaque σ-algebra:
  `∃ A Z C, IsPlaqueAlgebra (Uminus t) Z A ∧ μ Zᶜ = 0 ∧ comap φ A ≤ A ∧ (uniform bound) ∧
  HcondSig μ A ⊥ ≠ ⊤`.
  For the *cut* σ-algebras of the tree this fails: `A = descSig t (MSigW)` has atoms that are
  bounded `Uminus t`-plaques (`dim Uminus t ≤ 3` inside `dim X₃ = 8`, hence null) and
  `HcondSig μ A ⊥` is the entropy of the *transversal* (5-dimensional, atomless) leaf space, which
  is `⊤`; adding the coset-separating family `O` to generate the atoms makes the generators
  numerous but does not coarsen the transversal structure.  Pisa's 7.51–7.52 cure is to *cut
  transversally at the scale of the return time*: `Ω` a ball with thin boundary, the first-return
  partition `Q̃` of `Ω` (Pisa 7.49, in the tree: `firstReturn_partition`, `neverReturnSet_null`),
  each `Q_i` refined by a covering of `Ω` by `≤ c e^{κ i}` balls of radius `e^{-α i} r` (Pisa
  7.46), "smeared" in the `G⁻`-direction so that each piece is `Uminus t`-saturated inside a
  `V(e^{-α i} r)`-ball (Pisa 7.51).  Then
  `H_μ(P) ≤ H_μ(Q̃) + log c + κ Σ_i i μ(Q_i) < ∞` (Pisa 7.50/7.52, using `Σ_i i μ(Q_i) = 1`),
  while the `G⁻`-smearing makes the past atoms plaques (Pisa 7.53) and the two-sided shrinking
  makes the bi-orbit atoms singletons modulo `μ`.

The reduction below is *self-contained and proved*; it isolates exactly clause 3.

## STATUS (current session): the target is assembled; five route lemmas remain

The *whole* statement is now reduced to the **five** unproved declarations of
`Submission/Work/EKLC6Route/` (the route of `Submission/Work/EKLComp/C6GEOM_ROUTE_LEAD.md`,
`Work.EKLComp.C6GEOM_ROUTE_LEAD`), i.e. Pisa 7.43/7.46/7.50-7.54 in the form of that route.
A proof-term-closure scan (`#print axioms`-level, see `_eklc6_findsorry.lean` in the workspace
root) reports exactly

* `Work.EKLC6Route.exists_chart`   (L2a: a chart with measurable coordinates, uniform injectivity
  radius and a `μ`-thin `U`-shell at the chosen radius `r`),
* `Work.EKLC6Route.exists_window`  (L2b: the nested sub-windows `C j` of a chart),
* `Work.EKLC6Route.S_basic`        (L4a: `w.S` is a measurable partition, `w.N0` is null, `w.W`
  and `w.dU` are Borel, and the atoms of `w.A` are the fixed forward `w.S`-codes),
* `Work.EKLC6Route.plaque_data`    (L6: the conull Borel atom-saturated `Z` with
  `IsPlaqueAlgebra (Uminus t) Z w.A` and the uniform shape bound `2` on `Z ∩ w.W`,
  built from L4 (tracking), L5 (the lower bound / openness) and L6a (the a.e. margin)),
* `Work.EKLC6Route.tsum_negMulLog_ne_top` (L7: finite entropy of `σ (range w.S)`, Pisa 7.50+7.52).

Everything else in the proof-term closure of the target is `sorry`-free.

### How the target is assembled here

* `modmu_iSup_comap_neg_atom_singleton_ae_rec` — the singleton-atom statement
  `iSup_comap_neg_atom_singleton_ae` with the *uniform* shape bound on `Z` weakened to a bound on a
  subset `B ⊆ Z` that the backward orbit of a.e. point visits infinitely often (route L8).
  This is what lets the window construction bound the shape by `2` only on `Z ∩ w.W`: at the
  recurrent times `ψⁿ x ∈ Z ∩ w.W` the normed displacements `aDiag t ^ n * u n * (aDiag t ^ n)⁻¹`
  are the ones that shrink to `1` by `uniform_contraction_horo`.
* `exists_plaque_alg_gen_modmu_of_data_rec` — the reduction `..._of_data` in that recurrent form.
* the target itself: `exists_chart` → `exists_window` → `plaque_data` gives `Z`, the bound `2` on
  `Z ∩ w.W` and `0 < μ (Z ∩ w.W)`; `S_basic` gives the measurability/disjointness of `w.S` needed by
  `HcondSig_ne_top_of_tsum`, which together with `tsum_negMulLog_ne_top` supplies the entropy clause;
  `ae_frequently_mem_neg` (proved, and the only one of the five that is already `sorry`-free)
  supplies the recurrence of `Z ∩ w.W` from the ergodicity of `μ` and `0 < μ (Z ∩ w.W)`.
-/


open MeasureTheory Filter
open scoped ENNReal

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Two elementary atom facts -/

theorem modmu_mem_atom_self (m : MeasurableSpace X3) (x : X3) : x ∈ atom m x :=
  Set.mem_sInter.mpr fun _ hs => hs.2

theorem modmu_atom_mono {m m' : MeasurableSpace X3} (h : m ≤ m') (x : X3) :
    atom m' x ⊆ atom m x := by
  intro y hy
  rw [atom, Set.mem_sInter] at hy ⊢
  rintro s ⟨hs, hxs⟩
  exact hy s ⟨h s hs, hxs⟩

/-! ## Bookkeeping for the diagonal flow -/

/-- `aDiag (n • t) = (aDiag t) ^ n`. -/
theorem modmu_aDiag_nsmul (t : Fin 3 → ℝ) (n : ℕ) : aDiag (n • t) = aDiag t ^ n := by
  induction n with
  | zero => simp [aDiag_zero]
  | succ m ih =>
      rw [show (m + 1) • t = t + m • t from by rw [succ_nsmul, add_comm], ← aDiag_add, ih,
        pow_succ']

/-- The `n`-th iterate of `x ↦ aDiag t • x` is multiplication by `aDiag t ^ n`. -/
theorem modmu_iterate_aDiag (t : Fin 3 → ℝ) (n : ℕ) (y : X3) :
    ((fun x : X3 => aDiag t • x)^[n]) y = aDiag t ^ n • y := by
  induction n with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply', ih, ← mul_smul, ← pow_succ']

/-- `aDiag (-t) ^ n = (aDiag t ^ n)⁻¹`. -/
theorem modmu_aDiag_neg_pow (t : Fin 3 → ℝ) (n : ℕ) : aDiag (-t) ^ n = (aDiag t ^ n)⁻¹ := by
  rw [← modmu_aDiag_nsmul (-t) n, neg_nsmul, ← modmu_aDiag_nsmul t n]
  exact (inv_eq_of_mul_eq_one_left (aDiag_neg_mul (n • t))).symm

/-- The `n`-th iterate of `x ↦ aDiag (-t) • x` is multiplication by `(aDiag t ^ n)⁻¹`. -/
theorem modmu_iterate_aDiag_neg (t : Fin 3 → ℝ) (n : ℕ) (y : X3) :
    ((fun x : X3 => aDiag (-t) • x)^[n]) y = (aDiag t ^ n)⁻¹ • y := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, ← mul_smul]
      have hkey : aDiag (-t) * (aDiag t ^ m)⁻¹ = (aDiag t ^ (m + 1))⁻¹ := by
        have h1 : aDiag (-t) = (aDiag t)⁻¹ := by simpa using modmu_aDiag_neg_pow t 1
        rw [h1, pow_succ, mul_inv_rev]
      rw [hkey]

/-- `aDiag t ^ n` undoes the `n`-th iterate of `x ↦ aDiag (-t) • x`. -/
theorem modmu_smul_iterate_aDiag_neg (t : Fin 3 → ℝ) (n : ℕ) (y : X3) :
    aDiag t ^ n • (((fun x : X3 => aDiag (-t) • x)^[n]) y) = y := by
  rw [modmu_iterate_aDiag_neg, ← mul_smul, mul_inv_cancel, one_smul]


/-- `φ^[n]` and `ψ^[n]` are mutually inverse. -/
theorem modmu_comp_iterate_self (t : Fin 3 → ℝ) (n : ℕ) :
    ((fun x : X3 => aDiag t • x)^[n]) ∘ ((fun x : X3 => aDiag (-t) • x)^[n]) = id := by
  funext y
  rw [Function.comp_apply, modmu_iterate_aDiag, modmu_iterate_aDiag_neg, ← mul_smul,
    mul_inv_cancel, one_smul]
  rfl

/-- The composite of the inverse iterate with the direct iterate. -/
theorem modmu_comp_iterate_self' (t : Fin 3 → ℝ) (n : ℕ) :
    ((fun x : X3 => aDiag (-t) • x)^[n]) ∘ ((fun x : X3 => aDiag t • x)^[n]) = id := by
  funext y
  rw [Function.comp_apply, modmu_iterate_aDiag_neg, modmu_iterate_aDiag, ← mul_smul,
    inv_mul_cancel, one_smul]
  rfl


/-- The iterates of the flow and of its inverse commute. -/
theorem modmu_iterate_comm (t : Fin 3 → ℝ) (m n : ℕ) :
    ((fun x : X3 => aDiag t • x)^[m]) ∘ ((fun x : X3 => aDiag (-t) • x)^[n])
      = ((fun x : X3 => aDiag (-t) • x)^[n]) ∘ ((fun x : X3 => aDiag t • x)^[m]) := by
  funext y
  rw [Function.comp_apply, Function.comp_apply, modmu_iterate_aDiag, modmu_iterate_aDiag_neg,
    modmu_iterate_aDiag_neg, modmu_iterate_aDiag, ← mul_smul, ← mul_smul]
  congr 1
  have hm : aDiag t ^ m = aDiag (m • t) := (modmu_aDiag_nsmul t m).symm
  have hn : (aDiag t ^ n)⁻¹ = aDiag (-(n • t)) := by
    rw [← modmu_aDiag_neg_pow t n, ← modmu_aDiag_nsmul (-t) n, neg_nsmul]
  rw [hm, hn, aDiag_add, aDiag_add]
  exact congrArg aDiag (add_comm (m • t) (-(n • t)))

/-- `φ^[m] ∘ ψ^[n] = φ^[m - n]` for `n ≤ m`. -/
theorem modmu_comp_iterate_le {t : Fin 3 → ℝ} {n m : ℕ} (h : n ≤ m) :
    ((fun x : X3 => aDiag t • x)^[m]) ∘ ((fun x : X3 => aDiag (-t) • x)^[n])
      = ((fun x : X3 => aDiag t • x)^[m - n]) := by
  have hsplit : ((fun x : X3 => aDiag t • x)^[m])
      = ((fun x : X3 => aDiag t • x)^[m - n]) ∘ ((fun x : X3 => aDiag t • x)^[n]) := by
    conv_lhs => rw [show m = (m - n) + n from (Nat.sub_add_cancel h).symm]
    rw [Function.iterate_add]
  rw [hsplit, Function.comp_assoc, modmu_comp_iterate_self t n, Function.comp_id]

/-- `φ^[m] ∘ ψ^[n] = ψ^[n - m]` for `m ≤ n`. -/
theorem modmu_comp_iterate_ge {t : Fin 3 → ℝ} {n m : ℕ} (h : m ≤ n) :
    ((fun x : X3 => aDiag t • x)^[m]) ∘ ((fun x : X3 => aDiag (-t) • x)^[n])
      = ((fun x : X3 => aDiag (-t) • x)^[n - m]) := by
  have hsplit : ((fun x : X3 => aDiag (-t) • x)^[n])
      = ((fun x : X3 => aDiag (-t) • x)^[m]) ∘ ((fun x : X3 => aDiag (-t) • x)^[n - m]) := by
    conv_lhs => rw [show n = m + (n - m) from (Nat.add_sub_of_le h).symm]
    rw [Function.iterate_add]
  rw [hsplit, ← Function.comp_assoc, modmu_comp_iterate_self t m, Function.id_comp]

/-- **Measure preservation of the inverse flow.**  If `μ` is preserved by `φ = (aDiag t ·)` then it
is preserved by `x ↦ aDiag (-t) • x` (the two maps are mutually inverse). -/
theorem modmu_measurePreserving_aDiag_neg {μ : MeasureTheory.Measure X3} (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ) :
    MeasureTheory.MeasurePreserving (fun x : X3 => aDiag (-t) • x) μ μ := by
  have hφ : Measurable (fun x : X3 => aDiag t • x) := (continuous_const_smul (aDiag t)).measurable
  refine MeasureTheory.MeasurePreserving.mk (by fun_prop) ?_
  ext s hs
  rw [MeasureTheory.Measure.map_apply (by fun_prop) hs]
  have hsmul : ∀ z : X3, aDiag t • (aDiag (-t) • z) = z := by
    intro z
    rw [← mul_smul, aDiag_add, add_neg_cancel, aDiag_zero, one_smul]
  have himg : (fun x : X3 => aDiag (-t) • x) ⁻¹' s = (fun x : X3 => aDiag t • x) '' s := by
    ext z
    constructor
    · intro hz
      exact ⟨aDiag (-t) • z, hz, hsmul z⟩
    · rintro ⟨w, hw, rfl⟩
      simpa [aDiag_neg_smul] using hw
  rw [himg]
  have himgmeas : MeasurableSet ((fun x : X3 => aDiag t • x) '' s) := by
    rw [← himg]
    exact hs.preimage (by fun_prop)
  calc μ ((fun x : X3 => aDiag t • x) '' s)
      = (MeasureTheory.Measure.map (fun x : X3 => aDiag t • x) μ)
          ((fun x : X3 => aDiag t • x) '' s) := by rw [hmp.map_eq]
    _ = μ ((fun x : X3 => aDiag t • x) ⁻¹' ((fun x : X3 => aDiag t • x) '' s)) := by
          rw [MeasureTheory.Measure.map_apply hφ himgmeas]
    _ = μ s := by
          congr 1
          ext z
          constructor
          · rintro ⟨w, hw, hwz⟩
            have hwz' : w = z := MulAction.injective (aDiag t) hwz
            rwa [hwz'] at hw
          · intro hz
            exact ⟨z, hz, rfl⟩

/-- Membership in the atom of `⨆ n, comap (ψ^[n]) A`: the backward orbit stays in the atoms. -/
theorem modmu_mem_atom_iSup_comap {A : MeasurableSpace X3} {ψ : X3 → X3} (x y : X3) :
    y ∈ atom (⨆ n : ℕ, MeasurableSpace.comap (ψ^[n]) A) x ↔
      ∀ n : ℕ, (ψ^[n]) y ∈ atom A ((ψ^[n]) x) := by
  rw [atom_iSup_comap_iterate_eq A ψ x]
  exact Iff.rfl

/-! ## The atoms of `⨆ n, comap (ψ^[n]) A` are singletons a.e. (no singleton refinement) -/

/-- **The mod-`μ` generation without the singleton refinement.**  If `A` is a plaque algebra for
`Uminus t` on the conull set `Z` (with a *uniform* entrywise bound `C` on its shapes) and
`A` is `φ`-decreasing, then the σ-algebra `J = ⨆ n, comap (ψ^[n]) A` (with `ψ x = aDiag (-t) • x`
the inverse flow) has singleton atoms `μ`-almost everywhere — without assuming the atoms of `A`
to be singletons off `Z`.  Indeed the only points for which the proof of
`gen_atom_iSup_comap_iterate_neg_eq_singleton` needs that assumption are those whose backward
orbit leaves `Z`, and they form the `μ`-null set `⋃ n, ψ^{-n}(Zᶜ)`. -/
theorem iSup_comap_neg_atom_singleton_ae {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {A : MeasurableSpace X3} {Z : Set X3} {C : ℝ}
    (hZ : μ Zᶜ = 0)
    (hplq : IsPlaqueAlgebra (Uminus t) Z A)
    (hbnd : ∀ x ∈ Z, ∀ u ∈ Uminus t, u • x ∈ atom A x → ∀ i j, |u i j| ≤ C) :
    ∀ᵐ x ∂μ, atom (⨆ n : ℕ,
        MeasurableSpace.comap ((fun y : X3 => aDiag (-t) • y)^[n]) A) x = {x} := by
  letI : MeasurableSpace X3 := Work.EKLContract.instMeasurableSpaceX3
  classical
  set ψ : X3 → X3 := fun y => aDiag (-t) • y with hψdef
  -- the exceptional set: some backward iterate of `x` leaves `Z`
  have hmpψ : MeasureTheory.MeasurePreserving ψ μ μ := by
    rw [hψdef]
    exact modmu_measurePreserving_aDiag_neg t hmp
  have hnull : ∀ n : ℕ, μ (((ψ^[n]) ⁻¹' Z)ᶜ) = 0 := by
    intro n
    rw [← Set.preimage_compl]
    exact (hmpψ.iterate n).preimage_null hZ
  -- hence the union is null
  have hBad : μ (⋃ n : ℕ, ((ψ^[n]) ⁻¹' Z)ᶜ) = 0 := measure_iUnion_null hnull
  rw [MeasureTheory.ae_iff]
  refine le_antisymm ?_ bot_le
  calc μ {x : X3 | ¬ atom (⨆ n : ℕ,
          MeasurableSpace.comap ((fun y : X3 => aDiag (-t) • y)^[n]) A) x = {x}}
      ≤ μ (⋃ n : ℕ, ((ψ^[n]) ⁻¹' Z)ᶜ) := by
        refine MeasureTheory.measure_mono ?_
        intro x hx
        by_contra hcon
        -- all backward iterates of `x` lie in `Z`; show the atom is a singleton, contradiction
        have hxZ : ∀ n : ℕ, (ψ^[n]) x ∈ Z := by
          intro n
          by_contra hn
          exact hcon (Set.mem_iUnion.mpr ⟨n, by simpa [Set.mem_compl_iff, Set.mem_preimage] using hn⟩)
        have hJ : (⨆ n : ℕ, MeasurableSpace.comap (ψ^[n]) A) =
            (⨆ n : ℕ, MeasurableSpace.comap ((fun y : X3 => aDiag (-t) • y)^[n]) A) := by
          rw [hψdef]
        rw [hJ] at hx
        refine hx ?_
        refine Set.eq_singleton_iff_unique_mem.mpr ⟨modmu_mem_atom_self _ x, ?_⟩
        intro y hy
        have hy' : ∀ n : ℕ, (ψ^[n]) y ∈ atom A ((ψ^[n]) x) :=
          (modmu_mem_atom_iSup_comap x y).mp hy
        -- write `ψ^n y = u_n • ψ^n x` with `u_n` in the (uniformly bounded) shape
        have hU : ∀ n : ℕ, atom A ((ψ^[n]) x) ⊆
            (fun u : SL3 => u • ((ψ^[n]) x)) '' (Uminus t : Set SL3) :=
          fun n => (hplq.2.2.2 ((ψ^[n]) x) (hxZ n)).2.1
        choose u huU hux using fun n => hU n (hy' n)
        have hux' : ∀ n : ℕ, u n • ((ψ^[n]) x) = (ψ^[n]) y := fun n => hux n
        have hbnd' : ∀ n : ℕ, ∀ i j : Fin 3, |u n i j| ≤ C :=
          fun n i j => hbnd ((ψ^[n]) x) (hxZ n) (u n) (huU n)
            (by rw [hux' n]; exact hy' n) i j
        have hnorm : ∀ n : ℕ, aDiag t ^ n * u n * (aDiag t ^ n)⁻¹ ∈ Uminus t := by
          intro n
          have h := (uminus_isHoro t).1.2.1 (n • t) (u n) (huU n)
          rwa [modmu_aDiag_nsmul] at h
        have hy_eq : ∀ n : ℕ, y = (aDiag t ^ n * u n * (aDiag t ^ n)⁻¹) • x := by
          intro n
          rw [hψdef] at hux'
          have hψy : (ψ^[n]) y = (aDiag t ^ n)⁻¹ • y := modmu_iterate_aDiag_neg t n y
          have hψx : (ψ^[n]) x = (aDiag t ^ n)⁻¹ • x := modmu_iterate_aDiag_neg t n x
          have hundo : aDiag t ^ n • ((ψ^[n]) y) = y := modmu_smul_iterate_aDiag_neg t n y
          calc y = aDiag t ^ n • ((ψ^[n]) y) := hundo.symm
            _ = aDiag t ^ n • (u n • ((ψ^[n]) x)) := by rw [hux' n]
            _ = (aDiag t ^ n * u n) • ((ψ^[n]) x) := by rw [mul_smul]
            _ = (aDiag t ^ n * u n) • ((aDiag t ^ n)⁻¹ • x) := by rw [hψx]
            _ = (aDiag t ^ n * u n * (aDiag t ^ n)⁻¹) • x := by rw [← mul_smul]
        -- the uniform contraction
        obtain ⟨hsupp, hunif⟩ :=
          uniform_contraction_horo (U := Uminus t) (t := t) (uminus_isHoro t).2
        have hC1 : (1 : ℝ) ≤ C := by
          have h := hbnd x (hxZ 0) (1 : SL3) (Uminus t).one_mem
            (by rw [one_smul]; exact modmu_mem_atom_self A x) (0 : Fin 3) (0 : Fin 3)
          have h2 : |(1 : SL3) (0 : Fin 3) (0 : Fin 3)| = 1 := by
            rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq, abs_one]
          rwa [h2] at h
        have hVmem : ∀ n : ℕ, u n ∈ V (C + 1) := by
          intro n i j
          by_cases hij : i = j
          · subst hij
            have h1 : (u n : Matrix (Fin 3) (Fin 3) ℝ) i i =
                (1 : Matrix (Fin 3) (Fin 3) ℝ) i i := hsupp (u n) (huU n) i i le_rfl
            rw [h1, sub_self, abs_zero]
            linarith
          · have h1 : (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := Matrix.one_apply_ne hij
            have h2 : |(u n : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C := hbnd' n i j
            rw [h1, sub_zero]
            linarith
        have hconv : ∀ δ : ℝ, 0 < δ →
            ∀ᶠ n in Filter.atTop, aDiag t ^ n * u n * (aDiag t ^ n)⁻¹ ∈ V δ := by
          intro δ hδ
          obtain ⟨N, hN⟩ := hunif (C + 1) (by linarith) δ hδ
          exact Filter.eventually_atTop.mpr ⟨N, fun n hn' => hN n hn' (u n) (huU n) (hVmem n)⟩
        have htend : Filter.Tendsto (fun n : ℕ => aDiag t ^ n * u n * (aDiag t ^ n)⁻¹)
            Filter.atTop (nhds 1) :=
          Work.EKLComp.V_hasBasis_nhds_one.tendsto_right_iff.mpr hconv
        haveI : T2Space X3 := Work.EKLComp.X3Background.1
        have hcont : Continuous (fun u : SL3 => u • x) := by fun_prop
        have htend2 : Filter.Tendsto
            (fun n : ℕ => (aDiag t ^ n * u n * (aDiag t ^ n)⁻¹) • x)
            Filter.atTop (nhds ((1 : SL3) • x)) :=
          (hcont.tendsto (1 : SL3)).comp htend
        have hconst : (fun n : ℕ => (aDiag t ^ n * u n * (aDiag t ^ n)⁻¹) • x) =
            fun _ => y := by
          funext n
          exact (hy_eq n).symm
        have hfin : y = (1 : SL3) • x :=
          tendsto_nhds_unique (by rw [hconst]; exact tendsto_const_nhds) htend2
        simpa using hfin
    _ = 0 := hBad


/-- **A conull *Borel* set on which the atoms are singletons, from an a.e. statement.**  (Stated
in a context with no local `MeasurableSpace X₃` variable, so that the ambient Borel structure is
not captured.) -/
theorem exists_conull_borel_subset_of_ae_atom_singleton {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ) (S : ℕ → Set X3)
    (hae : ∀ᵐ x ∂μ, atom (biOrbit t S) x = {x}) :
    ∃ Z : Set X3, MeasurableSet Z ∧ μ Zᶜ = 0 ∧ ∀ x ∈ Z, atom (biOrbit t S) x = {x} := by
  have hnull : μ {x : X3 | ¬ atom (biOrbit t S) x = {x}} = 0 := MeasureTheory.ae_iff.mp hae
  obtain ⟨B, hBsub, hBmeas, hBμ⟩ :=
    MeasureTheory.exists_measurable_superset μ {x : X3 | ¬ atom (biOrbit t S) x = {x}}
  have hB0 : μ B = 0 := by rw [hBμ, hnull]
  refine ⟨Bᶜ, hBmeas.compl, ?_, fun x hx => ?_⟩
  · simpa using hB0
  · by_contra hcon
    exact hx (hBsub hcon)

/-! ## The reduction: the target from a *coarse* plaque algebra with finite entropy -/

/-- **The target from a plaque algebra of finite static entropy.**  If there are a countably
generated σ-algebra `A`, a conull `Z` and a uniform bound `C` with `A` a plaque algebra for
`Uminus t` on `Z`, `A` `φ`-decreasing and `HcondSig μ A ⊥ ≠ ⊤`, then the requested statement holds:
take `S` a countable generating sequence of `A` (possible since `A` is countably generated); then
`⨆ n, comap (φ^[n]) σ (range S) = A` (the `n = 0` term gives `⊇`, `φ`-decrease gives `⊆`), so the
first and third clauses hold, and `GeneratesModMuSet μ t S` follows from
`iSup_comap_neg_atom_singleton_ae` (applied to `A`) together with
`generatesModMuSet_of_atom_singleton` (the `ψ`-orbit σ-algebra is contained in the bi-orbit
σ-algebra, and the atoms of the bi-orbit σ-algebra are no larger). -/
theorem exists_plaque_alg_gen_modmu_of_coarse {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    (hcoarse : ∃ (A : MeasurableSpace X3) (Z : Set X3) (C : ℝ),
      IsPlaqueAlgebra (Uminus t) Z A ∧ μ Zᶜ = 0 ∧
      MeasurableSpace.comap (fun x : X3 => aDiag t • x) A ≤ A ∧
      (∀ x ∈ Z, ∀ u ∈ Uminus t, u • x ∈ atom A x → ∀ i j, |u i j| ≤ C) ∧
      @HcondSig X3 Work.EKLContract.instMeasurableSpaceX3 μ A
        (⊥ : MeasurableSpace X3) ≠ ⊤) :
    ∃ (S : ℕ → Set X3) (Z : Set X3),
      (∀ n : ℕ, MeasurableSet (S n)) ∧
      IsPlaqueAlgebra (Uminus t) Z
        (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
          (MeasurableSpace.generateFrom (Set.range S))) ∧
      μ Zᶜ = 0 ∧
      GeneratesModMuSet μ t S ∧
      HcondSig μ (MeasurableSpace.generateFrom (Set.range S))
        (⊥ : MeasurableSpace X3) ≠ ⊤ := by
  letI : MeasurableSpace X3 := Work.EKLContract.instMeasurableSpaceX3
  classical
  obtain ⟨A, Z, C, hplq, hZ, hdec, hbnd, hfin⟩ := hcoarse
  -- a countable generating sequence for `A`
  obtain ⟨e, he⟩ : ∃ e : ℕ → Set X3, A = MeasurableSpace.generateFrom (Set.range e) :=
    Work.EKLC6Geo.GPE.gen_exists_seq_generating_of_countable hplq.2.1
  have hσ : MeasurableSpace.generateFrom (Set.range e) = A := he.symm
  have hdec_n : ∀ n : ℕ,
      MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n]) A ≤ A := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        have hcomp : ((fun x : X3 => aDiag t • x)^[Nat.succ m])
            = (fun x : X3 => aDiag t • x) ∘ ((fun x : X3 => aDiag t • x)^[m]) := by
          funext y
          rw [Function.comp_apply, Function.iterate_succ_apply']
        rw [hcomp]
        have hcomp2 : MeasurableSpace.comap
              ((fun x : X3 => aDiag t • x) ∘ ((fun x : X3 => aDiag t • x)^[m])) A
            = MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[m])
                (MeasurableSpace.comap (fun x : X3 => aDiag t • x) A) :=
          MeasurableSpace.comap_comp.symm
        rw [hcomp2]
        exact le_trans (MeasurableSpace.comap_mono hdec) ih
  have hpast : (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
      (MeasurableSpace.generateFrom (Set.range e))) = A := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun n => ?_
      rw [hσ]
      exact hdec_n n
    · rw [← hσ]
      exact le_trans (le_of_eq (by rw [Function.iterate_zero, MeasurableSpace.comap_id]))
        (le_iSup (fun n : ℕ => MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
          (MeasurableSpace.generateFrom (Set.range e))) 0)
  -- the generators are measurable
  have hmeas : ∀ n : ℕ, MeasurableSet[Work.EKLContract.instMeasurableSpaceX3] (e n) := fun n =>
    hplq.1 (e n) (by rw [← hσ]; exact MeasurableSpace.measurableSet_generateFrom ⟨n, rfl⟩)
  -- the bi-orbit σ-algebra of `e` contains the `ψ`-orbit σ-algebra of `A`
  have hJle : (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag (-t) • x)^[n]) A) ≤
      biOrbit t e := by
    rw [biOrbit]
    refine iSup_le fun n => ?_
    rw [← hσ]
    exact le_trans le_sup_right (le_iSup (fun m : ℕ => MeasurableSpace.comap
        ((fun x : X3 => aDiag t • x)^[m]) (MeasurableSpace.generateFrom (Set.range e)) ⊔
      MeasurableSpace.comap ((fun x : X3 => aDiag (-t) • x)^[m])
        (MeasurableSpace.generateFrom (Set.range e))) n)
  -- the atoms of the `ψ`-orbit σ-algebra of `A` are singletons a.e.; hence so are those of the
  -- bi-orbit σ-algebra
  have haeJ : ∀ᵐ x ∂μ, atom (⨆ n : ℕ,
      MeasurableSpace.comap ((fun y : X3 => aDiag (-t) • y)^[n]) A) x = {x} :=
    iSup_comap_neg_atom_singleton_ae (μ := μ) t hmp hZ hplq hbnd
  have haeBi : ∀ᵐ x ∂μ, atom (biOrbit t e) x = {x} := by
    filter_upwards [haeJ] with x hx
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨modmu_mem_atom_self _ x, ?_⟩
    intro y hy
    have hmem : y ∈ atom (⨆ n : ℕ,
        MeasurableSpace.comap ((fun y : X3 => aDiag (-t) • y)^[n]) A) x :=
      modmu_atom_mono hJle x hy
    rw [hx] at hmem
    exact Set.mem_singleton_iff.mp hmem
  obtain ⟨Z', hZ'meas, hZ'c, hZ'good⟩ := exists_conull_borel_subset_of_ae_atom_singleton t e haeBi
  exact ⟨e, Z, hmeas, by rw [hpast]; exact hplq, hZ,
    generatesModMuSet_of_atom_singleton t e hmeas Z' hZ'meas hZ'c hZ'good,
    by rw [hσ]; exact hfin⟩

/-- **The sharp reduction.**  The requested statement follows from the *Pisa 7.43 geometric data*:
a countable Borel family `S`, a conull `Z` and a uniform bound `C` such that the *past* σ-algebra
`B = ⨆ₙ comap (φ^[n]) σ(S)` is a plaque algebra for `Uminus t` on `Z` (with shapes bounded by
`C`) and `σ (range S)` has finite static entropy.

The generation clause `GeneratesModMuSet μ t S` — which is *not* part of the data — is **derived
here** from the plaque structure by `iSup_comap_neg_atom_singleton_ae` (the `ψ`-orbit σ-algebra of
`B` has singleton atoms a.e., and it is contained in `biOrbit t S`) together with
`generatesModMuSet_of_atom_singleton`.  This is what makes the *modulo-`μ`* form of Pisa 7.43
provable without the (entropy-breaking) singleton refinement `exists_refine_singletons_g`: that
refinement is only needed for the *exact* equality `⨆ₙ comap (ψ^[n]) B = borel X₃`. -/
theorem exists_plaque_alg_gen_modmu_of_data {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    (hdata : ∃ (S : ℕ → Set X3) (Z : Set X3) (C : ℝ),
      (∀ n : ℕ, MeasurableSet[Work.EKLContract.instMeasurableSpaceX3] (S n)) ∧
      μ Zᶜ = 0 ∧
      IsPlaqueAlgebra (Uminus t) Z
        (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
          (MeasurableSpace.generateFrom (Set.range S))) ∧
      (∀ x ∈ Z, ∀ u ∈ Uminus t, u • x ∈
        atom (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
          (MeasurableSpace.generateFrom (Set.range S))) x → ∀ i j, |u i j| ≤ C) ∧
      @HcondSig X3 Work.EKLContract.instMeasurableSpaceX3 μ
        (MeasurableSpace.generateFrom (Set.range S)) (⊥ : MeasurableSpace X3) ≠ ⊤) :
    ∃ (S : ℕ → Set X3) (Z : Set X3),
      (∀ n : ℕ, MeasurableSet (S n)) ∧
      IsPlaqueAlgebra (Uminus t) Z
        (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
          (MeasurableSpace.generateFrom (Set.range S))) ∧
      μ Zᶜ = 0 ∧
      GeneratesModMuSet μ t S ∧
      HcondSig μ (MeasurableSpace.generateFrom (Set.range S)) (⊥ : MeasurableSpace X3) ≠ ⊤ := by
  letI : MeasurableSpace X3 := Work.EKLContract.instMeasurableSpaceX3
  classical
  obtain ⟨S, Z, C, hS, hZ, hplq, hbnd, hfin⟩ := hdata
  -- the past σ-algebra of `S`
  have hdecB : MeasurableSpace.comap (fun x : X3 => aDiag t • x)
        (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
          (MeasurableSpace.generateFrom (Set.range S)))
      ≤ (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
          (MeasurableSpace.generateFrom (Set.range S))) := by
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun n => ?_
    have hcomp : ((fun x : X3 => aDiag t • x)^[n + 1])
        = ((fun x : X3 => aDiag t • x)^[n]) ∘ (fun x : X3 => aDiag t • x) :=
      Function.iterate_succ (fun x : X3 => aDiag t • x) n
    rw [MeasurableSpace.comap_comp, ← hcomp]
    exact le_iSup (fun m : ℕ => MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[m])
      (MeasurableSpace.generateFrom (Set.range S))) (n + 1)
  -- the `ψ`-orbit σ-algebra of `B` is contained in the bi-orbit σ-algebra of `S`
  have hJle : (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag (-t) • x)^[n])
        (⨆ m : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[m])
          (MeasurableSpace.generateFrom (Set.range S)))) ≤ biOrbit t S := by
    rw [biOrbit]
    refine iSup_le fun n => ?_
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun m => ?_
    rcases Nat.le_total n m with h | h
    · rw [MeasurableSpace.comap_comp (f := ((fun x : X3 => aDiag t • x)^[m]))
          (g := ((fun x : X3 => aDiag (-t) • x)^[n])), modmu_comp_iterate_le h]
      exact le_trans le_sup_left (le_iSup (fun k : ℕ => MeasurableSpace.comap
          ((fun x : X3 => aDiag t • x)^[k]) (MeasurableSpace.generateFrom (Set.range S)) ⊔
        MeasurableSpace.comap ((fun x : X3 => aDiag (-t) • x)^[k])
          (MeasurableSpace.generateFrom (Set.range S))) (m - n))
    · rw [MeasurableSpace.comap_comp (f := ((fun x : X3 => aDiag t • x)^[m]))
          (g := ((fun x : X3 => aDiag (-t) • x)^[n])), modmu_comp_iterate_ge h]
      exact le_trans le_sup_right (le_iSup (fun k : ℕ => MeasurableSpace.comap
          ((fun x : X3 => aDiag t • x)^[k]) (MeasurableSpace.generateFrom (Set.range S)) ⊔
        MeasurableSpace.comap ((fun x : X3 => aDiag (-t) • x)^[k])
          (MeasurableSpace.generateFrom (Set.range S))) (n - m))
  -- the atoms of the `ψ`-orbit σ-algebra of the past are singletons a.e.
  have haeJ : ∀ᵐ x ∂μ, atom (⨆ n : ℕ, MeasurableSpace.comap
      ((fun y : X3 => aDiag (-t) • y)^[n])
      (⨆ m : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[m])
        (MeasurableSpace.generateFrom (Set.range S)))) x = {x} :=
    iSup_comap_neg_atom_singleton_ae (μ := μ) t hmp hZ hplq hbnd
  have haeBi : ∀ᵐ x ∂μ, atom (biOrbit t S) x = {x} := by
    filter_upwards [haeJ] with x hx
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨modmu_mem_atom_self _ x, ?_⟩
    intro y hy
    have hmem : y ∈ atom (⨆ n : ℕ, MeasurableSpace.comap ((fun y : X3 => aDiag (-t) • y)^[n])
        (⨆ m : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[m])
          (MeasurableSpace.generateFrom (Set.range S)))) x :=
      modmu_atom_mono hJle x hy
    rw [hx] at hmem
    exact Set.mem_singleton_iff.mp hmem
  obtain ⟨Z', hZ'meas, hZ'c, hZ'good⟩ := exists_conull_borel_subset_of_ae_atom_singleton t S haeBi
  exact ⟨S, Z, hS, hplq, hZ,
    generatesModMuSet_of_atom_singleton t S hS Z' hZ'meas hZ'c hZ'good, hfin⟩

/-! ## The singleton-atom statement with the bound only on a backward-recurrent set -/

/-- **Singleton atoms along the backward orbit, with the shape bound assumed only on a set `B`
revisited infinitely often.**  This is `modmu_iSup_comap_neg_atom_singleton_ae` with the uniform
bound on `Z` replaced by a bound on `B ⊆ Z` plus the recurrence hypothesis of the route's L8:
the backward orbit of a.e. `x` meets `B` infinitely often, so it suffices to control the shapes at
those (cofinally many) times. -/
theorem modmu_iSup_comap_neg_atom_singleton_ae_rec {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {A : MeasurableSpace X3} {Z B : Set X3} {C : ℝ}
    (hZ : μ Zᶜ = 0) (hBZ : B ⊆ Z)
    (hplq : IsPlaqueAlgebra (Uminus t) Z A)
    (hbnd : ∀ x ∈ B, ∀ u ∈ Uminus t, u • x ∈ atom A x → ∀ i j, |u i j| ≤ C)
    (hrec : ∀ᵐ x ∂μ, ∃ᶠ n in Filter.atTop,
      ((fun y : X3 => aDiag (-t) • y)^[n]) x ∈ B) :
    ∀ᵐ x ∂μ, atom (⨆ n : ℕ,
        MeasurableSpace.comap ((fun y : X3 => aDiag (-t) • y)^[n]) A) x = {x} := by
  letI : MeasurableSpace X3 := Work.EKLContract.instMeasurableSpaceX3
  classical
  set ψ : X3 → X3 := fun y => aDiag (-t) • y with hψdef
  have hmpψ : MeasureTheory.MeasurePreserving ψ μ μ := by
    rw [hψdef]
    exact modmu_measurePreserving_aDiag_neg t hmp
  have hnull : ∀ n : ℕ, μ (((ψ^[n]) ⁻¹' Z)ᶜ) = 0 := by
    intro n
    rw [← Set.preimage_compl]
    exact (hmpψ.iterate n).preimage_null hZ
  have hBad : μ (⋃ n : ℕ, ((ψ^[n]) ⁻¹' Z)ᶜ) = 0 := measure_iUnion_null hnull
  have haeZ : ∀ᵐ x ∂μ, ∀ n : ℕ, (ψ^[n]) x ∈ Z := by
    rw [MeasureTheory.ae_iff]
    refine le_antisymm (le_trans (MeasureTheory.measure_mono ?_) (le_of_eq hBad)) bot_le
    intro x hx
    rw [Set.mem_ofPred_eq, not_forall] at hx
    obtain ⟨n, hn⟩ := hx
    exact Set.mem_iUnion.mpr ⟨n, by simpa [Set.mem_preimage] using hn⟩
  filter_upwards [haeZ, hrec] with x hxZ hxB
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨modmu_mem_atom_self _ x, ?_⟩
  intro y hy
  -- cofinal sequence of return times of the backward orbit of `x` to `B`
  have hfreq : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (ψ^[n]) x ∈ B := fun N =>
    Filter.frequently_atTop.mp hxB N
  choose nseq hnseq_ge hnseq_B using hfreq
  have hJ : (⨆ n : ℕ, MeasurableSpace.comap (ψ^[n]) A) =
      (⨆ n : ℕ, MeasurableSpace.comap ((fun y : X3 => aDiag (-t) • y)^[n]) A) := by
    rw [hψdef]
  rw [hJ] at hy
  have hy' : ∀ n : ℕ, (ψ^[n]) y ∈ atom A ((ψ^[n]) x) :=
    (modmu_mem_atom_iSup_comap x y).mp hy
  have hU : ∀ n : ℕ, atom A ((ψ^[n]) x) ⊆
      (fun u : SL3 => u • ((ψ^[n]) x)) '' (Uminus t : Set SL3) :=
    fun n => (hplq.2.2.2 ((ψ^[n]) x) (hxZ n)).2.1
  choose u huU hux using fun n => hU n (hy' n)
  have hux' : ∀ n : ℕ, u n • ((ψ^[n]) x) = (ψ^[n]) y := fun n => hux n
  have hbnd' : ∀ N : ℕ, ∀ i j : Fin 3, |u (nseq N) i j| ≤ C :=
    fun N i j => hbnd ((ψ^[nseq N]) x) (hnseq_B N) (u (nseq N)) (huU (nseq N))
      (by rw [hux' (nseq N)]; exact hy' (nseq N)) i j
  have hnorm : ∀ n : ℕ, aDiag t ^ n * u n * (aDiag t ^ n)⁻¹ ∈ Uminus t := by
    intro n
    have h := (uminus_isHoro t).1.2.1 (n • t) (u n) (huU n)
    rwa [modmu_aDiag_nsmul] at h
  have hy_eq : ∀ n : ℕ, y = (aDiag t ^ n * u n * (aDiag t ^ n)⁻¹) • x := by
    intro n
    rw [hψdef] at hux'
    have hψy : (ψ^[n]) y = (aDiag t ^ n)⁻¹ • y := modmu_iterate_aDiag_neg t n y
    have hψx : (ψ^[n]) x = (aDiag t ^ n)⁻¹ • x := modmu_iterate_aDiag_neg t n x
    have hundo : aDiag t ^ n • ((ψ^[n]) y) = y := modmu_smul_iterate_aDiag_neg t n y
    calc y = aDiag t ^ n • ((ψ^[n]) y) := hundo.symm
      _ = aDiag t ^ n • (u n • ((ψ^[n]) x)) := by rw [hux' n]
      _ = (aDiag t ^ n * u n) • ((ψ^[n]) x) := by rw [mul_smul]
      _ = (aDiag t ^ n * u n) • ((aDiag t ^ n)⁻¹ • x) := by rw [hψx]
      _ = (aDiag t ^ n * u n * (aDiag t ^ n)⁻¹) • x := by rw [← mul_smul]
  obtain ⟨hsupp, hunif⟩ :=
    uniform_contraction_horo (U := Uminus t) (t := t) (uminus_isHoro t).2
  have hC1 : (1 : ℝ) ≤ C := by
    have h := hbnd ((ψ^[nseq 0]) x) (hnseq_B 0) (1 : SL3) (Uminus t).one_mem
      (by rw [one_smul]; exact modmu_mem_atom_self A _) (0 : Fin 3) (0 : Fin 3)
    have h2 : |(1 : SL3) (0 : Fin 3) (0 : Fin 3)| = 1 := by
      rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq, abs_one]
    rwa [h2] at h
  have hVmem : ∀ N : ℕ, u (nseq N) ∈ V (C + 1) := by
    intro N i j
    by_cases hij : i = j
    · subst hij
      have h1 : (u (nseq N) : Matrix (Fin 3) (Fin 3) ℝ) i i =
          (1 : Matrix (Fin 3) (Fin 3) ℝ) i i := hsupp (u (nseq N)) (huU (nseq N)) i i le_rfl
      rw [h1, sub_self, abs_zero]
      linarith
    · have h1 : (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := Matrix.one_apply_ne hij
      have h2 : |(u (nseq N) : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C := hbnd' N i j
      rw [h1, sub_zero]
      linarith
  have hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ N in Filter.atTop,
      aDiag t ^ (nseq N) * u (nseq N) * (aDiag t ^ (nseq N))⁻¹ ∈ V δ := by
    intro δ hδ
    obtain ⟨N₀, hN₀⟩ := hunif (C + 1) (by linarith) δ hδ
    refine Filter.eventually_atTop.mpr ⟨N₀, fun N hN => ?_⟩
    exact hN₀ (nseq N) (le_trans hN (hnseq_ge N)) (u (nseq N)) (huU (nseq N)) (hVmem N)
  have htend : Filter.Tendsto
      (fun N : ℕ => aDiag t ^ (nseq N) * u (nseq N) * (aDiag t ^ (nseq N))⁻¹)
      Filter.atTop (nhds 1) :=
    Work.EKLComp.V_hasBasis_nhds_one.tendsto_right_iff.mpr hconv
  haveI : T2Space X3 := Work.EKLComp.X3Background.1
  have hcont : Continuous (fun u : SL3 => u • x) := by fun_prop
  have htend2 : Filter.Tendsto
      (fun N : ℕ => (aDiag t ^ (nseq N) * u (nseq N) * (aDiag t ^ (nseq N))⁻¹) • x)
      Filter.atTop (nhds ((1 : SL3) • x)) :=
    (hcont.tendsto (1 : SL3)).comp htend
  have hconst : (fun N : ℕ =>
      (aDiag t ^ (nseq N) * u (nseq N) * (aDiag t ^ (nseq N))⁻¹) • x) = fun _ => y := by
    funext N
    exact (hy_eq (nseq N)).symm
  have hfin : y = (1 : SL3) • x :=
    tendsto_nhds_unique (by rw [hconst]; exact tendsto_const_nhds) htend2
  simpa using hfin

/-- **The sharp reduction, with a recurrent bound (route L8).**  Same as
`exists_plaque_alg_gen_modmu_of_data` except that the uniform shape bound is only assumed on a set
`B ⊆ Z` that the *backward* orbit of a.e. point visits infinitely often.  This is the form in
which the window construction of `C6GEOM_ROUTE_LEAD.md` produces its data: the bound `2` holds on
`Z ∩ W`, and the ergodicity of `μ` makes `Z ∩ W` backward-recurrent for a.e. point. -/
theorem exists_plaque_alg_gen_modmu_of_data_rec {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    (hdata : ∃ (S : ℕ → Set X3) (Z B : Set X3) (C : ℝ),
      (∀ n : ℕ, MeasurableSet[Work.EKLContract.instMeasurableSpaceX3] (S n)) ∧
      μ Zᶜ = 0 ∧
      IsPlaqueAlgebra (Uminus t) Z (pastSigSet t S) ∧
      B ⊆ Z ∧
      (∀ x ∈ B, ∀ u ∈ Uminus t, u • x ∈ atom (pastSigSet t S) x → ∀ i j, |u i j| ≤ C) ∧
      (∀ᵐ x ∂μ, ∃ᶠ n in Filter.atTop,
        ((fun y : X3 => aDiag (-t) • y)^[n]) x ∈ B) ∧
      @HcondSig X3 Work.EKLContract.instMeasurableSpaceX3 μ
        (MeasurableSpace.generateFrom (Set.range S)) (⊥ : MeasurableSpace X3) ≠ ⊤) :
    ∃ (S : ℕ → Set X3) (Z : Set X3),
      (∀ n : ℕ, MeasurableSet (S n)) ∧
      IsPlaqueAlgebra (Uminus t) Z
        (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
          (MeasurableSpace.generateFrom (Set.range S))) ∧
      μ Zᶜ = 0 ∧
      GeneratesModMuSet μ t S ∧
      HcondSig μ (MeasurableSpace.generateFrom (Set.range S)) (⊥ : MeasurableSpace X3) ≠ ⊤ := by
  letI : MeasurableSpace X3 := Work.EKLContract.instMeasurableSpaceX3
  classical
  obtain ⟨S, Z, B, C, hS, hZ, hplq, hBZ, hbnd, hrec, hfin⟩ := hdata
  have hdecB : MeasurableSpace.comap (fun x : X3 => aDiag t • x)
        (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
          (MeasurableSpace.generateFrom (Set.range S)))
      ≤ (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
          (MeasurableSpace.generateFrom (Set.range S))) := by
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun n => ?_
    have hcomp : ((fun x : X3 => aDiag t • x)^[n + 1])
        = ((fun x : X3 => aDiag t • x)^[n]) ∘ (fun x : X3 => aDiag t • x) :=
      Function.iterate_succ (fun x : X3 => aDiag t • x) n
    rw [MeasurableSpace.comap_comp, ← hcomp]
    exact le_iSup (fun m : ℕ => MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[m])
      (MeasurableSpace.generateFrom (Set.range S))) (n + 1)
  have hJle : (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag (-t) • x)^[n])
        (⨆ m : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[m])
          (MeasurableSpace.generateFrom (Set.range S)))) ≤ biOrbit t S := by
    rw [biOrbit]
    refine iSup_le fun n => ?_
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun m => ?_
    rcases Nat.le_total n m with h | h
    · rw [MeasurableSpace.comap_comp (f := ((fun x : X3 => aDiag t • x)^[m]))
          (g := ((fun x : X3 => aDiag (-t) • x)^[n])), modmu_comp_iterate_le h]
      exact le_trans le_sup_left (le_iSup (fun k : ℕ => MeasurableSpace.comap
          ((fun x : X3 => aDiag t • x)^[k]) (MeasurableSpace.generateFrom (Set.range S)) ⊔
        MeasurableSpace.comap ((fun x : X3 => aDiag (-t) • x)^[k])
          (MeasurableSpace.generateFrom (Set.range S))) (m - n))
    · rw [MeasurableSpace.comap_comp (f := ((fun x : X3 => aDiag t • x)^[m]))
          (g := ((fun x : X3 => aDiag (-t) • x)^[n])), modmu_comp_iterate_ge h]
      exact le_trans le_sup_right (le_iSup (fun k : ℕ => MeasurableSpace.comap
          ((fun x : X3 => aDiag t • x)^[k]) (MeasurableSpace.generateFrom (Set.range S)) ⊔
        MeasurableSpace.comap ((fun x : X3 => aDiag (-t) • x)^[k])
          (MeasurableSpace.generateFrom (Set.range S))) (n - m))
  have haeJ : ∀ᵐ x ∂μ, atom (⨆ n : ℕ, MeasurableSpace.comap
      ((fun y : X3 => aDiag (-t) • y)^[n])
      (⨆ m : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[m])
        (MeasurableSpace.generateFrom (Set.range S)))) x = {x} :=
    modmu_iSup_comap_neg_atom_singleton_ae_rec (μ := μ) t hmp hZ hBZ hplq hbnd hrec
  have haeBi : ∀ᵐ x ∂μ, atom (biOrbit t S) x = {x} := by
    filter_upwards [haeJ] with x hx
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨modmu_mem_atom_self _ x, ?_⟩
    intro y hy
    have hmem : y ∈ atom (⨆ n : ℕ, MeasurableSpace.comap ((fun y : X3 => aDiag (-t) • y)^[n])
        (⨆ m : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[m])
          (MeasurableSpace.generateFrom (Set.range S)))) x :=
      modmu_atom_mono hJle x hy
    rw [hx] at hmem
    exact Set.mem_singleton_iff.mp hmem
  obtain ⟨Z', hZ'meas, hZ'c, hZ'good⟩ := exists_conull_borel_subset_of_ae_atom_singleton t S haeBi
  exact ⟨S, Z, hS, hplq, hZ,
    generatesModMuSet_of_atom_singleton t S hS Z' hZ'meas hZ'c hZ'good, hfin⟩


/-! ## The target -/

theorem exists_plaque_alg_gen_modmu {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hqerg : ∀ E : Set Work.EKLContract.X3, MeasurableSet E →
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ⁻¹' E =ᵐ[μ] E →
      μ E = 0 ∨ μ Eᶜ = 0)
    (hU : Work.EKLC6Core.Uminus t ≠ ⊥) :
    ∃ (S : ℕ → Set Work.EKLContract.X3) (Z : Set Work.EKLContract.X3),
      (∀ n : ℕ, MeasurableSet (S n)) ∧
      Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z
        (⨆ n : ℕ, MeasurableSpace.comap
          ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n])
          (MeasurableSpace.generateFrom (Set.range S))) ∧
      μ Zᶜ = 0 ∧
      Work.EKLC6Core.GeneratesModMuSet μ t S ∧
      Work.EKLC6Core.HcondSig μ (MeasurableSpace.generateFrom (Set.range S))
        (⊥ : MeasurableSpace Work.EKLContract.X3) ≠ ⊤ := by
  letI : MeasurableSpace X3 := Work.EKLContract.instMeasurableSpaceX3
  classical
  -- L2a + L2b of `C6GEOM_ROUTE_LEAD.md`: a chart and a window over it
  obtain ⟨c⟩ := Work.EKLC6Route.exists_chart (μ := μ) t
  obtain ⟨w, -⟩ := Work.EKLC6Route.exists_window (μ := μ) c
  -- L6: the conull good set, with the uniform shape bound `2` on `Z ∩ w.W`
  obtain ⟨Z, hZm, hZ, hplq, hpos, hbnd⟩ := Work.EKLC6Route.plaque_data (μ := μ) w hmp hqerg
  have hbasic := Work.EKLC6Route.S_basic (μ := μ) w hmp
  have hWmeas : MeasurableSet w.W := hbasic.2.2.2.2.1
  have hBmeas : MeasurableSet (Z ∩ w.W) := hZm.inter hWmeas
  -- L8a: `Z ∩ w.W` is backward-recurrent
  have hrec := Work.EKLC6Route.ae_frequently_mem_neg (μ := μ) hmp hqerg hBmeas hpos
  -- L7: finite entropy of the one-step σ-algebra
  have hent : @Work.EKLC6Core.HcondSig X3 Work.EKLContract.instMeasurableSpaceX3 μ
      (MeasurableSpace.generateFrom (Set.range w.S)) (⊥ : MeasurableSpace X3) ≠ ⊤ :=
    Work.EKLC6Core.HcondSig_ne_top_of_tsum (μ := μ) w.S hbasic.1 hbasic.2.1
      (Work.EKLC6Route.tsum_negMulLog_ne_top (μ := μ) w hmp)
  exact exists_plaque_alg_gen_modmu_of_data_rec (μ := μ) t hmp
    ⟨w.S, Z, Z ∩ w.W, 2, hbasic.1, hZ, hplq, Set.inter_subset_left,
      (fun x hx u hu hux i j => hbnd x hx u hu hux i j), hrec, hent⟩

end Work.EKLC6Core

end
