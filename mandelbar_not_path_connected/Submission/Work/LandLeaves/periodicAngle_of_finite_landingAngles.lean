/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# Periodicity of the angle of a ray landing at a repelling point, from finiteness

Let `T_c z = z̄² + c` be the tricorn map, `φ` a Böttcher coordinate of `T_c`, `y` a *repelling*
periodic point of odd period `k` (`Work.Landing.IsRepelling c k y`), and `θ` the angle of a
dynamic ray whose accumulation set is the singleton `{y}`.  Assume moreover that only *finitely*
many angles of rays accumulate at `y`:

`{ψ | rayAccum c φ ψ = {y}} ∩ Ico 0 1` is finite.

Then some positive multiple `2 * k * q` of `2 * k` is a period of the angle `Int.fract θ` under
angle doubling: `Work.Landing.PeriodicAngle (Int.fract θ) (2 * k * q)`.

## The argument

Let `S = {ψ | rayAccum c φ ψ = {y}} ∩ Ico 0 1` be the set of *normalised* landing angles of `y`,
finite by hypothesis.  The holomorphic second return map `τ = (T_c)^[2k]` fixes `y`, so it
transfers the ray at angle `θ` to the ray at angle `angDouble^[2k] θ`:

`T_c^[2k] '' rayAccum c φ θ = rayAccum c φ (angDouble^[2k] θ)`

(`Work.Landing.rayAccum_iterate`); hence the *second-return angle map*
`B = angDouble^[2k]` maps `S` into itself, and even lands in the canonical interval `[0,1)`
because `B x = Int.fract (4^k x)` (`angDouble_iterate_two_mul`).  This gives a self-map `F` of the
finite type `S`.

`F` is **injective** on `S`: if `B ψ = B ψ'` with `ψ, ψ' ∈ S`, then `4^k ψ ≡ 4^k ψ' (mod 1)`, and
since both rays accumulate at the repelling point `y`, the two angles are congruent modulo `1`
(`eq_mod_one_of_rayAccum_of_angDouble_eq`, the injectivity of the angle map on the type of a
repelling periodic point); as both lie in `[0,1)` they are equal.

Now `S` is finite, so the `N + 1` elements `θ₀, F θ₀, …, F^[N] θ₀` of `S` (`N = card S`) cannot
all be distinct: `F^[a] θ₀ = F^[b] θ₀` for some `a < b`.  Injectivity of `F^[a]` then upgrades this
to `F^[b-a] θ₀ = θ₀`.  Undoing the definition of `F` (the underlying value of `F^[n] ψ` is
`B^[n] ψ.1`) and using `B^[q] = angDouble^[2k*q]` (`Function.iterate_mul`) gives
`angDouble^[2k*(b-a)] (Int.fract θ) = Int.fract θ`.

Note that injectivity is *not* a luxury: for a mere self-map of a finite set the orbit need only be
eventually periodic, so the conclusion is genuinely stronger than the pigeonhole step.
-/
import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.isPreconnected_rayAccum
import Submission.Work.LandLeaves.exists_preimage_rayAccum
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq
import Submission.Work.LandLeaves.periodicAngle_of_landsAt_isRepelling

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Classical

theorem periodicAngle_of_finite_landingAngles {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ} {θ : ℝ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    (hland : Work.Landing.rayAccum c φ θ = {y})
    (hfin : ({ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} ∩ Set.Ico 0 1).Finite) :
    ∃ q : ℕ, 0 < q ∧ Work.Landing.PeriodicAngle (Int.fract θ) (2 * k * q) := by
  have hk : 0 < k := hrep.1.1
  -- * the (finite) set of normalised landing angles at `y`
  set S : Set ℝ := {ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} ∩ Set.Ico 0 1 with hS
  have hSmem : ∀ ψ : ℝ, ψ ∈ S ↔ Work.Landing.rayAccum c φ ψ = {y} ∧ 0 ≤ ψ ∧ ψ < 1 := by
    intro ψ
    rw [hS, Set.mem_inter_iff, Set.mem_Ico]
    exact Iff.rfl
  -- * the second-return angle map `B = angDouble^[2k]`, whose value form is `fract (4^k ·)`
  set B : ℝ → ℝ := Work.Landing.angDouble^[2 * k] with hB
  have hBfract : ∀ x : ℝ, B x = Int.fract ((4 : ℝ) ^ k * x) := by
    intro x
    rw [hB]
    exact angDouble_iterate_two_mul hk x
  -- * the canonical representative of the angle `θ`
  have hθmem : Int.fract θ ∈ S := by
    rw [hSmem]
    exact ⟨by rw [rayAccum_fract]; exact hland, Int.fract_nonneg θ, Int.fract_lt_one θ⟩
  have hSfinType : Fintype S := hfin.fintype
  set θ₀ : S := ⟨Int.fract θ, hθmem⟩ with hθ₀
  have hθ₀val : θ₀.1 = Int.fract θ := rfl
  -- * the second-return angle map is a self-map of `S`
  have hBmem : ∀ ψ : S, B ψ.1 ∈ S := by
    intro ψ
    rw [hSmem]
    refine ⟨?_, ?_, ?_⟩
    · have h1 : B ψ.1 = Work.Landing.angDouble^[2 * k] ψ.1 := by rw [hB]
      rw [h1]
      exact rayAccum_angDouble_of_isRepelling hφ hrep ((hSmem ψ.1).mp ψ.2).1
    · rw [hBfract]; exact Int.fract_nonneg _
    · rw [hBfract]; exact Int.fract_lt_one _
  let F : S → S := fun ψ => ⟨B ψ.1, hBmem ψ⟩
  -- * the underlying value of an iterate of `F`
  have hval : ∀ (n : ℕ) (ψ : S), (F^[n] ψ).1 = B^[n] ψ.1 := by
    intro n ψ
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact congrArg B ih
  -- * `F` is injective: distinct landing angles at `y` stay distinct under `B`
  have hFinj : Function.Injective F := by
    intro ψ₁ ψ₂ heq
    refine Subtype.ext ?_
    have hBeq : B ψ₁.1 = B ψ₂.1 := congrArg Subtype.val heq
    rw [hBfract, hBfract] at hBeq
    obtain ⟨m, hm⟩ := Int.fract_eq_fract.mp hBeq
    obtain ⟨mm, hmm⟩ := eq_mod_one_of_rayAccum_of_angDouble_eq hφ hrep
      ((hSmem ψ₁.1).mp ψ₁.2).1 ((hSmem ψ₂.1).mp ψ₂.2).1 ⟨m, by linarith⟩
    have h₁ := ((hSmem ψ₁.1).mp ψ₁.2).2
    have h₂ := ((hSmem ψ₂.1).mp ψ₂.2).2
    have hmmz : mm = 0 := by
      have hlt : (mm : ℝ) < 1 := by linarith [hmm, h₁.2, h₂.2]
      have hgt : (-1 : ℝ) < (mm : ℝ) := by linarith [hmm, h₁.1, h₂.1]
      have hlt' : mm < 1 := by exact_mod_cast hlt
      have hgt' : -1 < mm := by exact_mod_cast hgt
      omega
    rw [hmmz, Int.cast_zero, add_zero] at hmm
    exact hmm
  -- * pigeonhole: the orbit of `θ₀` in the finite set `S` repeats
  set N : ℕ := Fintype.card S with hN
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun n : Fin (N + 1) => F^[n.1] θ₀)
    (by rw [Fintype.card_fin, hN]; exact Nat.lt_succ_self _)
  have hne : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
  -- * injectivity upgrades the repeat to a genuine return of `θ₀`
  have key : ∀ a b : ℕ, a < b → F^[a] θ₀ = F^[b] θ₀ → F^[b - a] θ₀ = θ₀ := by
    intro a b hab h
    have hinj : Function.Injective (F^[a]) := hFinj.iterate a
    apply hinj
    rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hab.le]
    exact h.symm
  have hBpow : ∀ q : ℕ, B^[q] = Work.Landing.angDouble^[2 * k * q] := by
    intro q
    rw [hB]
    exact (Function.iterate_mul Work.Landing.angDouble (2 * k) q).symm
  have final : ∀ a b : ℕ, a < b → F^[a] θ₀ = F^[b] θ₀ →
      Work.Landing.PeriodicAngle (Int.fract θ) (2 * k * (b - a)) := by
    intro a b hab h
    have hper : F^[b - a] θ₀ = θ₀ := key a b hab h
    have hv : B^[b - a] (Int.fract θ) = Int.fract θ := by
      rw [← hθ₀val, ← hval (b - a) θ₀, congrArg Subtype.val hper]
    rw [Work.Landing.PeriodicAngle, ← hBpow (b - a)]
    exact hv
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨j.1 - i.1, Nat.sub_pos_of_lt hlt, final i.1 j.1 hlt heq⟩
  · exact ⟨i.1 - j.1, Nat.sub_pos_of_lt hgt, final j.1 i.1 hgt heq.symm⟩

end Work.LandLeaves
