import Mathlib
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq
import Submission.Work.LandLeaves.finite_of_closedInCircle_invariant_injective

import Mathlib
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq
import Submission.Work.LandLeaves.finite_of_closedInCircle_invariant_injective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Clash-free copy of `Submission/Work/LandLeaves/exists_periodicAngle_of_backward_orbit_cluster`

A verbatim copy, in the namespace `Work.LandLeaves.V2Anchor`, of the combinatorial core of the
anchor: a closed `σ`-invariant subset of the circle on which `σ = angDouble^[2k]` is injective and
surjective is finite, hence contains a periodic point; the point is an angle whose ray accumulates
exactly at `y` by the covering hypothesis `hcov`.  The copy drops the (unused) `AnchorHelpers`
import of the original, so that it coexists with the cyclic-order-preservation vocabulary of

`Submission.Work.LandLeaves.ccBet_v2_defs`.
-/



namespace Work.LandLeaves.V2Anchor

noncomputable section

open Filter Set
open scoped Topology

section Helpers

/-- `(n ↦ (n:ℝ)+1)⁻¹ → 0`. -/
lemma tendsto_nat_add_one_inv : Tendsto (fun j : ℕ => ((j:ℝ)+1)⁻¹) atTop (𝓝 0) := by
  have h1 : Tendsto (fun j : ℕ => (((j + 1 : ℕ)) : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
        (StrictMono.tendsto_atTop (fun a b h => by omega)))
  simpa [Nat.cast_add, Nat.cast_one] using h1

/-- **The fractional part is determined by its limit along a convergent sequence.**
If `y j → X` and `Int.fract (y j) → W` then `Int.fract X = Int.fract W`.  (The limit `W` need not
lie in `[0,1)`: it can be `1`, which is the fractional part of an integer limit.) -/
lemma fract_eq_fract_of_tendsto {y : ℕ → ℝ} {X W : ℝ}
    (hX : Tendsto y atTop (𝓝 X)) (hW : Tendsto (fun j => Int.fract (y j)) atTop (𝓝 W)) :
    Int.fract X = Int.fract W := by
  refine Int.fract_eq_fract.mpr ?_
  have hZ : Tendsto (fun j => ((⌊y j⌋ : ℤ) : ℝ)) atTop (𝓝 (X - W)) := by
    have h1 : Tendsto (fun j => y j - Int.fract (y j)) atTop (𝓝 (X - W)) := hX.sub hW
    simpa only [Int.self_sub_fract] using h1
  have hmem : ∀ j, ((⌊y j⌋ : ℤ) : ℝ) ∈ Set.range ((↑) : ℤ → ℝ) := fun j => ⟨⌊y j⌋, rfl⟩
  obtain ⟨z, hz⟩ :=
    IsClosed.mem_of_tendsto Real.isClosed_range_intCast hZ (Eventually.of_forall hmem)
  exact ⟨z, hz.symm⟩

/-- A point of the closed tail-cluster set `⋂ N, closure (f '' Ici N)` is the limit of a sequence
of values of `f` along indices tending to infinity. -/
lemma exists_seq_tendsto_of_mem_closure_tails {α : Type*} [PseudoMetricSpace α]
    {f : ℕ → α} {q : α} (h : ∀ N : ℕ, q ∈ closure (f '' Set.Ici N)) :
    ∃ u : ℕ → ℕ, (∀ j, j ≤ u j) ∧ Tendsto (f ∘ u) atTop (𝓝 q) := by
  have hex : ∀ j : ℕ, ∃ m : ℕ, j ≤ m ∧ dist (f m) q < ((j:ℝ)+1)⁻¹ := by
    intro j
    obtain ⟨z, hz, hd⟩ := Metric.mem_closure_iff.mp (h j) (((j:ℝ)+1)⁻¹) (by positivity)
    obtain ⟨m, hm, rfl⟩ := hz
    exact ⟨m, hm, by rwa [dist_comm] at hd⟩
  refine ⟨fun j => Classical.choose (hex j), fun j => (Classical.choose_spec (hex j)).1, ?_⟩
  have hb : ∀ j, dist (f (Classical.choose (hex j))) q < ((j:ℝ)+1)⁻¹ :=
    fun j => (Classical.choose_spec (hex j)).2
  rw [tendsto_iff_dist_tendsto_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_nat_add_one_inv
    (fun j => dist_nonneg) (fun j => le_of_lt (hb j))

/-- `b - 1 ∈ Set.Ici N` when `N + 1 ≤ b`. -/
lemma mem_Ici_sub_one {N b : ℕ} (h : N + 1 ≤ b) : b - 1 ∈ Set.Ici N := by
  simp only [Set.mem_Ici]; omega

end Helpers

/-- **A periodic angle from a backward orbit of angles whose tail-cluster points all land at `y`.**

`β : ℕ → ℝ` takes values in `[0,1)` and is a *backward orbit* of the `2k`-fold angle map
`σ := (angDouble)^[2k]` (so `σ θ = Int.fract (4^k * θ)`): `β n = σ (β (n+1))`.
`hcov` says every point of the closed tail-cluster set `C := ⋂ N, closure (β '' Set.Ici N)`
is an angle whose ray has accumulation set `{y}` (this is what the sibling result
`Work.LandLeaves.cluster_rayAccum_eq_singleton` provides; `hrep` is a repelling periodic point).

CONSTRUCTION SKETCH (do NOT use `Work.LandLeaves.exists_periodicAngle_of_rayAccum_singleton` or
`Work.LandLeaves.isClosed_rayAccum_singleton`: both still contain an unfinished proof and would poison the
axiom footprint; and `Work.LandLeaves.finite_type_of_orderPreserving` is FALSE as stated and does
not build -- the abstract order-preserving route is unsound, see
`Submission/Work/LandLeaves/NOTES_FALSE_tupling_injective_mod_one_on_closure.md`).
Use `Work.LandLeaves.finite_of_closedInCircle_invariant_injective`
(`Submission/Work/LandLeaves/finite_of_closedInCircle_invariant_injective.lean`):

* `C` is closed (an intersection of closed sets), contained in `[0,1]` (`hβ01`), and nonempty
  (`IsCompact.tendsto_subseq` applied to `β` in `Set.Icc 0 1`). In fact `1 ∉ C`: if `β ∘ u → 1`
  for a strictly monotone `u`, a convergent subsequence of `j ↦ β (u j + 1)` gives `p` with
  `σ p = 1` (continuity of `σ`), contradicting `σ p = Int.fract (4^k * p) < 1`. So `C ⊆ Set.Ico 0 1`.
* `σ '' C ⊆ C`: for `x ∈ C` and every `N`, `β '' Set.Ici N = σ '' (β '' Set.Ici (N+1))`
  (from `hβ`), and `σ '' closure A ⊆ closure (σ '' A)`
  (`image_closure_subset_closure_image`, continuity of `σ`).
* `C ⊆ σ '' C`: given `q ∈ C`, choose a strictly monotone `u` with `β ∘ u → q`
  (`Metric.mem_closure_iff` + recursion: `q ∈ closure (β '' Set.Ici N)` for every `N`), then take a
  convergent subsequence `β (u (ψ j) + 1) → p` (`IsCompact.tendsto_subseq` in `[0,1]`);
  `p ∈ C` and `σ p = q` by continuity.
* Injectivity of `σ` on `C`: if `x, y ∈ C` and `σ x = σ y`, then
  `Int.fract_eq_fract` gives `m : ℤ` with `4^k * x = 4^k * y + m`, and
  `Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq hφ hrep (hcov x hxC) (hcov y hyC) ⟨m, _⟩`
  gives `mm : ℤ` with `x = y + mm`; both lie in `[0,1)` so `x = y`.
* Apply the finiteness result with `d := 4^k` (`2 ≤ 4^k` from `0 < k = hrep.1.1`) and `K := C`:
  `hsub` is `C ⊆ Set.Ico 0 1`, `hclosed` is `1 ∉ C` plus closedness, `hmap`/`hsurj`/`hinj` as above.
  Get `C.Finite`.
* On the finite type `C`, the map `x ↦ σ x` is injective (`hinj`), hence bijective
  (`Finite.injective_iff_surjective`); pick `p ∈ C` (`C` nonempty) and use pigeonhole
  (`Fintype.exists_ne_map_eq_of_card_lt`) on `i ↦ (σ^[i] p)` to get `i < j` with the same value,
  hence `σ^[q] p = p` for `q = j - i > 0` (`Function.Injective.iterate`).
* Conclude with `t := p`: `Int.fract t = t` since `t ∈ [0,1)`,
  `rayAccum c φ t = {y}` by `hcov`, and
  `(angDouble)^[2*k*q] (Int.fract t) = ((angDouble)^[2*k])^[q] t = σ^[q] p = p`
  (`Function.iterate_mul`, `Work.LandLeaves.angDouble_iterate_two_mul` for `angDouble^[2k] = σ`,
  `0 < k`). -/
theorem exists_periodicAngle_of_backward_orbit_cluster {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    {β : ℕ → ℝ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    (hβ01 : ∀ n : ℕ, β n ∈ Set.Ico (0 : ℝ) 1)
    (hβ : ∀ n : ℕ, β n = (Work.Landing.angDouble)^[2 * k] (β (n + 1)))
    (hcov : ∀ x : ℝ, (∀ N : ℕ, x ∈ closure (β '' Set.Ici N)) →
      Work.Landing.rayAccum c φ x = {y}) :
    ∃ q : ℕ, 0 < q ∧ ∃ t : ℝ,
      Work.Landing.PeriodicAngle (Int.fract t) (2 * k * q) ∧
      Work.Landing.rayAccum c φ t = {y} := by
  have hk : 0 < k := hrep.1.1
  have hβIcc : ∀ n : ℕ, β n ∈ Set.Icc (0:ℝ) 1 :=
    fun n => ⟨(hβ01 n).1, le_of_lt (hβ01 n).2⟩
  -- the closed tail-cluster set
  let C : Set ℝ := ⋂ N, closure (β '' Set.Ici N)
  have hCmem : ∀ x : ℝ, x ∈ C ↔ ∀ N, x ∈ closure (β '' Set.Ici N) := fun x => Set.mem_iInter
  have hCclosed : IsClosed C := isClosed_iInter (fun N => isClosed_closure)
  have hCne : C.Nonempty := by
    obtain ⟨p, hp, ψ, hψ, hψt⟩ := isCompact_Icc.tendsto_subseq hβIcc
    refine ⟨p, (hCmem p).mpr fun N => ?_⟩
    refine isClosed_closure.mem_of_tendsto hψt ?_
    filter_upwards [eventually_ge_atTop N] with j hj
    exact subset_closure ⟨ψ j, le_trans hj (hψ.id_le j), rfl⟩
  have hCsub : C ⊆ Set.Icc (0:ℝ) 1 := by
    intro x hx
    exact closure_minimal (fun z hz => by obtain ⟨n, -, rfl⟩ := hz; exact hβIcc n) isClosed_Icc
      ((hCmem x).mp hx 0)
  by_cases h1C : (1:ℝ) ∈ C
  · -- if `1 ∈ C` the answer is immediate: the angle `1` is periodic of period `0` and its ray
    -- accumulates at `y`.
    refine ⟨1, one_pos, 1, ?_, hcov 1 ((hCmem 1).mp h1C)⟩
    have hfix : Work.Landing.angDouble 0 = 0 := by simp [Work.Landing.angDouble]
    show (Work.Landing.angDouble)^[2 * k * 1] (Int.fract 1) = Int.fract 1
    rw [Int.fract_one]
    exact Function.iterate_fixed hfix (2 * k * 1)
  · have h1notC : ¬ ((1:ℝ) ∈ C) := h1C
    have hsub : ∀ x ∈ C, 0 ≤ x ∧ x < 1 := by
      intro x hx
      refine ⟨(hCsub hx).1, lt_of_le_of_ne (hCsub hx).2 ?_⟩
      intro hx1
      exact h1notC (hx1 ▸ hx)
    -- `σ '' C ⊆ C`
    have hmap : ∀ x ∈ C, (Work.Landing.angDouble)^[2*k] x ∈ C := by
      intro x hx
      refine (hCmem _).mpr fun N => ?_
      have hex : ∀ j : ℕ, ∃ m : ℕ, max (N+1) j ≤ m ∧ dist (β m) x < ((j:ℝ)+1)⁻¹ := by
        intro j
        obtain ⟨z, hz, hd⟩ := Metric.mem_closure_iff.mp ((hCmem x).mp hx (max (N+1) j))
          (((j:ℝ)+1)⁻¹) (by positivity)
        obtain ⟨m, hm, rfl⟩ := hz
        exact ⟨m, hm, by rwa [dist_comm] at hd⟩
      let m : ℕ → ℕ := fun j => Classical.choose (hex j)
      have hm_spec : ∀ j, max (N+1) j ≤ m j ∧ dist (β (m j)) x < ((j:ℝ)+1)⁻¹ :=
        fun j => Classical.choose_spec (hex j)
      have hm_ge : ∀ j, j ≤ m j := fun j => le_trans (le_max_right _ _) (hm_spec j).1
      have hm_geN : ∀ j, N + 1 ≤ m j := fun j => le_trans (le_max_left _ _) (hm_spec j).1
      have hb : ∀ j, dist (β (m j)) x < ((j:ℝ)+1)⁻¹ := fun j => (hm_spec j).2
      have htend_m : Tendsto (fun j => β (m j)) atTop (𝓝 x) := by
        rw [tendsto_iff_dist_tendsto_zero]
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_nat_add_one_inv
          (fun j => dist_nonneg) (fun j => le_of_lt (hb j))
      have hmem2 : ∀ j, β (m j - 1) ∈ Set.Icc (0:ℝ) 1 := fun j => hβIcc _
      obtain ⟨w, hwIcc, χ, hχ, hχt⟩ := isCompact_Icc.tendsto_subseq hmem2
      have hχt' : Tendsto (fun j => β (m (χ j))) atTop (𝓝 x) := htend_m.comp hχ.tendsto_atTop
      have hy1 : Tendsto (fun j => (4:ℝ)^k * β (m (χ j))) atTop (𝓝 ((4:ℝ)^k * x)) :=
        (tendsto_const_nhds (x := (4:ℝ)^k)).mul hχt'
      have hy2 : Tendsto (fun j => Int.fract ((4:ℝ)^k * β (m (χ j)))) atTop (𝓝 w) := by
        have heq : (fun j => Int.fract ((4:ℝ)^k * β (m (χ j)))) = fun j => β (m (χ j) - 1) := by
          funext j
          have h1 : (Work.Landing.angDouble)^[2*k] (β (m (χ j))) = β (m (χ j) - 1) := by
            have h2 : m (χ j) - 1 + 1 = m (χ j) := by have := hm_geN (χ j); omega
            conv_lhs => rw [← h2]
            exact (hβ (m (χ j) - 1)).symm
          rw [← angDouble_iterate_two_mul hk (β (m (χ j)))]
          exact h1
        rw [heq]
        exact hχt
      have hpinning : Int.fract ((4:ℝ)^k * x) = Int.fract w := fract_eq_fract_of_tendsto hy1 hy2
      rcases lt_or_eq_of_le hwIcc.2 with hwlt | hweq
      · have hσx : (Work.Landing.angDouble)^[2*k] x = w := by
          rw [angDouble_iterate_two_mul hk x, hpinning, Int.fract_eq_self.mpr ⟨hwIcc.1, hwlt⟩]
        rw [hσx]
        refine isClosed_closure.mem_of_tendsto hχt (Eventually.of_forall fun j => ?_)
        refine subset_closure ?_
        exact ⟨m (χ j) - 1, mem_Ici_sub_one (hm_geN (χ j)), rfl⟩
      · -- the limit `w = 1` would put `1` into `C`, contradicting `1 ∉ C`
        exfalso
        have h1mem : ∀ M, (1:ℝ) ∈ closure (β '' Set.Ici M) := by
          intro M
          rw [← hweq]
          refine isClosed_closure.mem_of_tendsto hχt ?_
          filter_upwards [eventually_ge_atTop (M+1)] with j hj
          have hjχ : j ≤ χ j := hχ.id_le j
          have hmj : j ≤ m (χ j) := le_trans hjχ (hm_ge (χ j))
          exact subset_closure ⟨m (χ j) - 1, mem_Ici_sub_one (by omega), rfl⟩
        exact h1notC ((hCmem 1).mpr h1mem)
    -- `C ⊆ σ '' C`
    have hsurj : ∀ q ∈ C, ∃ x ∈ C, (Work.Landing.angDouble)^[2*k] x = q := by
      intro q hq
      obtain ⟨u, hu_ge, hut⟩ := exists_seq_tendsto_of_mem_closure_tails (f := β) ((hCmem q).mp hq)
      have hmem2 : ∀ j, β (u j + 1) ∈ Set.Icc (0:ℝ) 1 := fun j => hβIcc _
      obtain ⟨p, hpIcc, ψ, hψ, hψt⟩ := isCompact_Icc.tendsto_subseq hmem2
      have hpC : p ∈ C := by
        refine (hCmem p).mpr fun M => ?_
        refine isClosed_closure.mem_of_tendsto hψt ?_
        filter_upwards [eventually_ge_atTop M] with j hj
        refine subset_closure ⟨u (ψ j) + 1, Set.mem_Ici.mpr ?_, rfl⟩
        have h1 : j ≤ ψ j := hψ.id_le j
        have h2 : ψ j ≤ u (ψ j) := hu_ge (ψ j)
        omega
      have hσp : (Work.Landing.angDouble)^[2*k] p = q := by
        have hy1 : Tendsto (fun j => (4:ℝ)^k * β (u (ψ j) + 1)) atTop (𝓝 ((4:ℝ)^k * p)) :=
          (tendsto_const_nhds (x := (4:ℝ)^k)).mul hψt
        have hy2 : Tendsto (fun j => Int.fract ((4:ℝ)^k * β (u (ψ j) + 1))) atTop (𝓝 q) := by
          have heq : (fun j => Int.fract ((4:ℝ)^k * β (u (ψ j) + 1))) = fun j => β (u (ψ j)) := by
            funext j
            rw [← angDouble_iterate_two_mul hk (β (u (ψ j) + 1)), ← hβ (u (ψ j))]
          rw [heq]
          exact hut.comp hψ.tendsto_atTop
        have hpinning : Int.fract ((4:ℝ)^k * p) = Int.fract q := fract_eq_fract_of_tendsto hy1 hy2
        rw [angDouble_iterate_two_mul hk p, hpinning, Int.fract_eq_self.mpr (hsub q hq)]
      exact ⟨p, hpC, hσp⟩
    -- injectivity of `σ` on `C`
    have hinj : ∀ x ∈ C, ∀ y ∈ C,
        (Work.Landing.angDouble)^[2*k] x = (Work.Landing.angDouble)^[2*k] y → x = y := by
      intro x hx y hy hxy
      have hfrac : Int.fract ((4:ℝ)^k * x) = Int.fract ((4:ℝ)^k * y) := by
        rw [← angDouble_iterate_two_mul hk x, ← angDouble_iterate_two_mul hk y, hxy]
      obtain ⟨m, hm⟩ := Int.fract_eq_fract.mp hfrac
      obtain ⟨mm, hmm⟩ := eq_mod_one_of_rayAccum_of_angDouble_eq hφ hrep
        (hcov x ((hCmem x).mp hx)) (hcov y ((hCmem y).mp hy)) ⟨m, by linarith⟩
      have hx0 : 0 ≤ x := (hsub x hx).1
      have hx1 : x < 1 := (hsub x hx).2
      have hy0 : 0 ≤ y := (hsub y hy).1
      have hy1 : y < 1 := (hsub y hy).2
      have hmmR : x - y = (mm:ℝ) := by linarith
      have hmm0 : mm = 0 := by
        rcases lt_trichotomy mm 0 with h | h | h
        · have hle : ((mm:ℤ):ℝ) ≤ -1 := by
            have : mm ≤ -1 := by omega
            exact_mod_cast this
          linarith
        · exact h
        · have hge : (1:ℝ) ≤ (mm:ℝ) := by
            have : (1:ℤ) ≤ mm := by omega
            exact_mod_cast this
          linarith
      rw [hmm0] at hmmR
      simp at hmmR
      linarith
    -- finiteness of `C`
    have hfin : C.Finite := by
      refine finite_of_closedInCircle_invariant_injective (d := 4^k) ?_ hCne hsub ?_ ?_ ?_ ?_
      · calc (2:ℕ) ≤ 4 := by norm_num
          _ = 4^1 := (pow_one 4).symm
          _ ≤ 4^k := Nat.pow_le_pow_right (by norm_num) hk
      · exact hCclosed.union isClosed_singleton
      · intro x hx
        have h := hmap x hx
        simpa only [angDouble_iterate_two_mul hk x, Nat.cast_pow, Nat.cast_ofNat] using h
      · intro yy hy
        obtain ⟨x, hx, hxy⟩ := hsurj yy hy
        exact ⟨x, hx, by simpa only [angDouble_iterate_two_mul hk x, Nat.cast_pow, Nat.cast_ofNat] using hxy⟩
      · intro x hx y hy h
        refine hinj x hx y hy ?_
        simpa only [angDouble_iterate_two_mul hk x, angDouble_iterate_two_mul hk y, Nat.cast_pow, Nat.cast_ofNat] using h
    -- a periodic point of the restricted map
    haveI : Fintype C := hfin.fintype
    obtain ⟨p, hpC⟩ := hCne
    let p₀ : C := ⟨p, hpC⟩
    let σc : C → C := fun z => ⟨(Work.Landing.angDouble)^[2*k] z.1, hmap z.1 z.2⟩
    have hσcinj : Function.Injective σc := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      exact Subtype.ext (hinj a ha b hb (congrArg Subtype.val hab))
    have hiter_val : ∀ (i : ℕ) (z : C),
        (σc^[i] z).1 = (((Work.Landing.angDouble)^[2*k])^[i]) z.1 := by
      intro i
      induction i with
      | zero => intro z; rfl
      | succ i ih =>
        intro z
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (σc z)]
    have hcard : Fintype.card C < Fintype.card (Fin (Fintype.card C + 1)) := by
      rw [Fintype.card_fin]; exact Nat.lt_succ_self _
    obtain ⟨i, j, hij_ne, hij_eq⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (Fintype.card C + 1) => σc^[i.1] p₀) hcard
    obtain ⟨ii, jj, hlt, heq⟩ : ∃ ii jj : ℕ, ii < jj ∧ σc^[ii] p₀ = σc^[jj] p₀ := by
      have hij : (i:Fin _).1 ≠ j.1 := fun h => hij_ne (Fin.ext h)
      rcases lt_or_gt_of_ne hij with h | h
      · exact ⟨i.1, j.1, h, hij_eq⟩
      · exact ⟨j.1, i.1, h, hij_eq.symm⟩
    have hfix : σc^[jj - ii] p₀ = p₀ := by
      have h1 : σc^[ii] (σc^[jj - ii] p₀) = σc^[jj] p₀ := by
        rw [← Function.iterate_add_apply σc ii (jj - ii) p₀,
          show ii + (jj - ii) = jj by omega]
      rw [← heq] at h1
      exact hσcinj.iterate ii h1
    refine ⟨jj - ii, by omega, p, ?_, hcov p ((hCmem p).mp hpC)⟩
    have hval : (((Work.Landing.angDouble)^[2*k])^[jj-ii]) p = p :=
      (hiter_val (jj - ii) p₀).symm.trans (congrArg Subtype.val hfix)
    show (Work.Landing.angDouble)^[2 * k * (jj - ii)] (Int.fract p) = Int.fract p
    rw [Int.fract_eq_self.mpr (hsub p hpC), Function.iterate_mul]
    exact hval

end

end Work.LandLeaves.V2Anchor

