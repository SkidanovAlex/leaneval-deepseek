import Mathlib
import Submission.Work.LANDCL.Defs
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.rayAccum_entry
import Submission.Work.LandLeaves.dynBottcherOnlyOnMandelbar
import Submission.Work.LandLeaves.exists_local_repelling_branch
import Submission.Work.LandLeaves.isPreconnected_rayAccum
import Submission.Work.LandLeaves.isDynBottcherHomeo_of_isDynBottcher
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq
import Submission.Work.LandLeaves.exists_preimage_rayAccum
import Submission.Work.LandLeaves.finite_of_closedInCircle_invariant_injective
import Submission.Work.LandLeaves.isClosed_rayAccum_singleton

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false



/-! ## `Work.LandLeaves.periodicAngle_of_landsAt_isRepelling`

**The statement.**  For a parameter `c` with a Böttcher coordinate `φ` of the tricorn map
`T_c z = z̄² + c`, if `y` is a repelling periodic point of odd period `k` and the dynamic ray at
angle `θ` accumulates exactly at `y`, then the class of `θ` modulo `1` is periodic of period
dividing `2 * k * q` for some `q > 0`.

**The proof, and where its pieces live.**

1. *The angle data depends on the angle only modulo `1`* (`radialRay_add_int`, `dynRay_add_int`,
   `rayAccum_add_int`, `rayAccum_add_one`, `rayAccum_fract` below): this is why the conclusion is
   stated for `Int.fract θ`.
2. *The return map transfers rays* (`rayAccum_angDouble_of_isRepelling` below): the holomorphic
   second return map `τ = (T_c)^[2k]` fixes `y`, so it carries the ray at `θ` to the ray at
   `σ θ := angDouble^[2k] θ = Int.fract (4^k θ)`.  Hence `σ` maps the type
   `A := {ψ | rayAccum c φ ψ = {y}}` into itself.
3. *Finiteness of the type* (`finite_typeAngles` below, assembled from the delegated lemmas):
   * `Work.LandLeaves.isClosed_rayAccum_singleton` — `A` is closed (a limit of rays landing at
     `y` again lands at `y`; the local model at the repelling point `y` is what forbids a second
     accumulation point);
   * `Work.LandLeaves.exists_preimage_rayAccum` — `σ` is surjective on `A` (mod `1`);
   * `Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq` — `σ` is injective on `A` (mod `1`);
   * `Work.LandLeaves.finite_of_closedInCircle_invariant_injective` — a subset of the circle,
     closed in the circle, invariant under the `d`-tupling map and injective for it, is finite.
4. *Finiteness implies periodicity* (`periodicAngle_of_finite_type` below): `σ` is a bijection of
   the finite set `A ∩ [0,1)`, so the orbit of `Int.fract θ` is periodic there.

This is the "residual gap" in Goldberg–Milnor B.1 (the finiteness of the *type* of a repelling
periodic point, Goldberg–Milnor, *Fixed points of polynomial maps II*, Lemma 2.2, proved here
without the classical hypothesis that some *rational* ray lands at the point). -/

namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Angle-periodicity of the ray data

`rayAccum`, `dynRay` and `radialRay` depend on the angle only through the direction
`rayDirection θ = e^{2πiθ}`, hence only through the class of `θ` modulo `1`.  This is what makes
the angle `Int.fract θ` the canonical representative in the conclusion of the main theorem. -/

/-- The radial line at angle `θ` depends on `θ` only modulo `1`. -/
theorem radialRay_add_int (θ : ℝ) (m : ℤ) :
    Work.Landing.radialRay (θ + (m : ℝ)) = Work.Landing.radialRay θ := by
  ext w
  simp only [Work.Landing.radialRay, Set.mem_setOf_eq]
  have hdir : Work.Landing.rayDirection (θ + (m : ℝ)) = Work.Landing.rayDirection θ :=
    Work.Landing.Rays.rayDirection_eq_of_sub_int ⟨m, rfl⟩
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, by rw [hdir]⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, by rw [hdir]⟩

/-- The dynamic ray at angle `θ` depends on `θ` only modulo `1`. -/
theorem dynRay_add_int (c : ℂ) (φ : ℂ → ℂ) (θ : ℝ) (m : ℤ) :
    Work.Landing.dynRay c φ (θ + (m : ℝ)) = Work.Landing.dynRay c φ θ := by
  ext z
  simp only [Work.Landing.dynRay, Set.mem_setOf_eq]
  rw [radialRay_add_int]

/-- The accumulation set of the ray at angle `θ` depends on `θ` only modulo `1`; in particular
`rayAccum c φ (Int.fract θ) = rayAccum c φ θ`. -/
theorem rayAccum_add_int (c : ℂ) (φ : ℂ → ℂ) (θ : ℝ) (m : ℤ) :
    Work.Landing.rayAccum c φ (θ + (m : ℝ)) = Work.Landing.rayAccum c φ θ := by
  unfold Work.Landing.rayAccum
  simp only [dynRay_add_int]

/-- `rayAccum c φ` is invariant under `θ ↦ θ + 1`. -/
theorem rayAccum_add_one (c : ℂ) (φ : ℂ → ℂ) (θ : ℝ) :
    Work.Landing.rayAccum c φ (θ + 1) = Work.Landing.rayAccum c φ θ := by
  simpa using rayAccum_add_int c φ θ 1

/-- `rayAccum c φ` evaluated at the canonical representative of the angle. -/
theorem rayAccum_fract (c : ℂ) (φ : ℂ → ℂ) (θ : ℝ) :
    Work.Landing.rayAccum c φ (Int.fract θ) = Work.Landing.rayAccum c φ θ := by
  have h : θ = Int.fract θ + ((⌊θ⌋ : ℤ) : ℝ) := by
    have := Int.self_sub_fract (a := θ); linarith
  conv_rhs => rw [h]
  exact (rayAccum_add_int c φ (Int.fract θ) ⌊θ⌋).symm

/-! ## The return map preserves the angles of rays landing at `y`

`τ := (T_c)^{2k} = (Tsq c)^[k]` fixes the repelling periodic point `y`, so the transfer
`T_c^{2k} '' rayAccum c φ θ = rayAccum c φ (angDouble^[2k] θ)` maps the angle `θ` of a ray
landing at `y` to another such angle.  This is the *inclusion* half of the statement that the
angle map permutes the set `{θ : rayAccum c φ θ = {y}}`; the surjectivity and injectivity halves
are the delegated lemmas `Work.LandLeaves.exists_preimage_rayAccum` and
`Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq`. -/
theorem rayAccum_angDouble_of_isRepelling {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ} {θ : ℝ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    (h : Work.Landing.rayAccum c φ θ = {y}) :
    Work.Landing.rayAccum c φ ((Work.Landing.angDouble)^[2 * k] θ) = {y} := by
  obtain ⟨hper, -⟩ := hrep
  have h2k : (Tantibar c)^[2 * k] y = y := by
    rw [show 2 * k = k + k from by ring, Function.iterate_add_apply, hper.2, hper.2]
  rw [Work.Landing.rayAccum_iterate hφ θ (2 * k), h, Set.image_singleton, h2k]


/-! ## The type of a repelling periodic point, and cyclic betweenness

`typeAngles c φ y` is the set of angles of dynamic rays whose accumulation set is the singleton
`{y}` — the *type* of `y`.  `ccBetween a b x` says that `x` lies on the counterclockwise open
arc from `a` to `b`. -/

/-- The **type** of the point `y` (for the Böttcher coordinate `φ`): the real angles of rays
whose accumulation set is the singleton `{y}`. -/
def typeAngles (c : ℂ) (φ : ℂ → ℂ) (y : ℂ) : Set ℝ :=
  {ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}}

/-- `x` lies on the counterclockwise open arc from `a` to `b` (modulo `1`). -/
def ccBetween (a b x : ℝ) : Prop := ∃ n : ℤ, a < x + n ∧ x + n < b


/-! ## Finiteness of the type implies periodicity of the angle

The classical argument: the second-return angle map `σ = angDouble^[2k] = fun t => Int.fract (4^k t)`
maps the *finite* set `S = {ψ | rayAccum c φ ψ = {y}} ∩ Ico 0 1` into itself
(`rayAccum_angDouble_of_isRepelling`), and is injective on it
(`eq_mod_one_of_rayAccum_of_angDouble_eq`); hence the `σ`-orbit of `Int.fract θ` is periodic in the
finite set `S`, and undoing the definition of `σ` gives the periodicity of the angle. -/
theorem periodicAngle_of_finite_type {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ} {θ : ℝ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    (hland : Work.Landing.rayAccum c φ θ = {y})
    (hfin : ({ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} ∩ Set.Ico 0 1).Finite) :
    ∃ q : ℕ, 0 < q ∧ Work.Landing.PeriodicAngle (Int.fract θ) (2 * k * q) := by
  have hk : 0 < k := hrep.1.1
  set S : Set ℝ := {ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} ∩ Set.Ico 0 1 with hS
  have hSmem : ∀ ψ : ℝ, ψ ∈ S ↔ Work.Landing.rayAccum c φ ψ = {y} ∧ 0 ≤ ψ ∧ ψ < 1 := by
    intro ψ
    rw [hS, Set.mem_inter_iff, Set.mem_Ico]
    exact Iff.rfl
  set B : ℝ → ℝ := Work.Landing.angDouble^[2 * k] with hB
  have hBfract : ∀ x : ℝ, B x = Int.fract ((4 : ℝ) ^ k * x) := by
    intro x
    rw [hB]
    exact angDouble_iterate_two_mul hk x
  have hθmem : Int.fract θ ∈ S := by
    rw [hSmem]
    exact ⟨by rw [rayAccum_fract]; exact hland, Int.fract_nonneg θ, Int.fract_lt_one θ⟩
  have hSfinType : Fintype S := hfin.fintype
  set θ₀ : S := ⟨Int.fract θ, hθmem⟩ with hθ₀
  have hθ₀val : θ₀.1 = Int.fract θ := rfl
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
  have hval : ∀ (n : ℕ) (ψ : S), (F^[n] ψ).1 = B^[n] ψ.1 := by
    intro n ψ
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact congrArg B ih
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
  set N : ℕ := Fintype.card S with hN
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun n : Fin (N + 1) => F^[n.1] θ₀)
    (by rw [Fintype.card_fin, hN]; exact Nat.lt_succ_self _)
  have hne : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
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

/-! ## Finiteness of the type, from closedness and the coding lemma

The type `A = {ψ | rayAccum c φ ψ = {y}}` is closed (`isClosed_rayAccum_singleton`) and
`1`-periodic (`rayAccum_add_int`), so `K := A ∩ Ico 0 1` is closed *in the circle* (`K ∪ {1}` is
closed in `ℝ`).  The second-return angle map `σ = fun t => Int.fract (4^k t)` maps `K` into itself
(`rayAccum_angDouble_of_isRepelling`), is surjective on it (`exists_preimage_rayAccum`) and
injective on it (`eq_mod_one_of_rayAccum_of_angDouble_eq`), so the coding lemma
`finite_of_closedInCircle_invariant_injective` gives finiteness of the normalised type. -/

/-- `Int.fract (n * Int.fract θ) = Int.fract (n * θ)` for a natural number `n`. -/
private theorem fract_mul_fract (n : ℕ) (θ : ℝ) :
    Int.fract ((n : ℝ) * Int.fract θ) = Int.fract ((n : ℝ) * θ) := by
  have h1 : θ = Int.fract θ + (⌊θ⌋ : ℤ) := by
    have := Int.self_sub_fract (a := θ); linarith
  have h2 : (n : ℝ) * θ = (n : ℝ) * Int.fract θ + ((n * ⌊θ⌋ : ℤ) : ℝ) := by
    conv_lhs => rw [h1]
    push_cast
    ring
  rw [h2, Int.fract_add_intCast]

/-- **Finiteness of the type of a repelling periodic point** (finitely many rays land at `y`). -/
theorem finite_typeAngles {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y) :
    ({ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} ∩ Set.Ico 0 1).Finite := by
  have hk : 0 < k := hrep.1.1
  set A : Set ℝ := {ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} with hA
  have hAcl : IsClosed A := isClosed_rayAccum_singleton hφ hrep
  set K : Set ℝ := A ∩ Set.Ico 0 1 with hK
  have hKmem : ∀ ψ : ℝ, ψ ∈ K ↔
      Work.Landing.rayAccum c φ ψ = {y} ∧ 0 ≤ ψ ∧ ψ < 1 := by
    intro ψ
    simp only [hK, hA, Set.mem_inter_iff, Set.mem_Ico, Set.mem_setOf_eq]
  have hcl : IsClosed (K ∪ {1}) := by
    have heq : K ∪ {1} = (A ∩ Set.Icc 0 1) ∪ {1} := by
      ext x
      simp only [hK, Set.mem_union, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_Ico,
        Set.mem_Icc]
      constructor
      · rintro (⟨hx, h1, h2⟩ | hx1)
        · exact Or.inl ⟨hx, h1, le_of_lt h2⟩
        · exact Or.inr hx1
      · rintro (⟨hx, h1, h2⟩ | hx1)
        · rcases eq_or_lt_of_le h2 with h3 | h3
          · exact Or.inr h3
          · exact Or.inl ⟨hx, h1, h3⟩
        · exact Or.inr hx1
    rw [heq]
    exact (hAcl.inter isClosed_Icc).union isClosed_singleton
  have hfin : K.Finite := by
    rcases K.eq_empty_or_nonempty with hemp | hne
    · rw [hemp]; exact Set.finite_empty
    refine finite_of_closedInCircle_invariant_injective (d := 4 ^ k) ?_ hne ?_ hcl ?_ ?_ ?_
    · calc (2 : ℕ) ≤ 4 := by norm_num
        _ ≤ 4 ^ k := Nat.le_self_pow hk.ne' 4
    · intro x hx
      exact ⟨(hKmem x).mp hx |>.2.1, (hKmem x).mp hx |>.2.2⟩
    · intro x hx
      have hx' : Work.Landing.rayAccum c φ x = {y} := (hKmem x).mp hx |>.1
      have hone : Work.Landing.rayAccum c φ (Int.fract ((4 : ℝ) ^ k * x)) = {y} := by
        have h2 : (Work.Landing.angDouble)^[2 * k] x = Int.fract ((4 : ℝ) ^ k * x) :=
          angDouble_iterate_two_mul hk x
        rw [← h2]
        exact rayAccum_angDouble_of_isRepelling hφ hrep hx'
      rw [hKmem]
      exact ⟨by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hone,
        Int.fract_nonneg _, Int.fract_lt_one _⟩
    · intro y' hy'
      have hy'' : Work.Landing.rayAccum c φ y' = {y} := (hKmem y').mp hy' |>.1
      have hyb : 0 ≤ y' ∧ y' < 1 := ⟨(hKmem y').mp hy' |>.2.1, (hKmem y').mp hy' |>.2.2⟩
      obtain ⟨θ', hθ', m, hm⟩ := exists_preimage_rayAccum hφ hrep hy''
      refine ⟨Int.fract θ', ?_, ?_⟩
      · rw [hKmem]
        exact ⟨by rw [rayAccum_fract]; exact hθ', Int.fract_nonneg θ', Int.fract_lt_one θ'⟩
      · have hm' : ((4 ^ k : ℕ) : ℝ) * θ' = y' + m := by
          simpa only [Nat.cast_pow, Nat.cast_ofNat] using hm
        exact (by
          rw [fract_mul_fract (4 ^ k) θ', hm', Int.fract_add_intCast,
            Int.fract_eq_self.mpr hyb] :
          Int.fract (((4 ^ k : ℕ) : ℝ) * Int.fract θ') = y')
    · intro x hx y' hy' hxy
      have hx' : Work.Landing.rayAccum c φ x = {y} := (hKmem x).mp hx |>.1
      have hy'' : Work.Landing.rayAccum c φ y' = {y} := (hKmem y').mp hy' |>.1
      have hxy' : Int.fract ((4 : ℝ) ^ k * x) = Int.fract ((4 : ℝ) ^ k * y') := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hxy
      obtain ⟨m, hm⟩ := Int.fract_eq_fract.mp hxy'
      have hm2 : (4 : ℝ) ^ k * x = (4 : ℝ) ^ k * y' + m := by linarith [hm]
      obtain ⟨mm, hmm⟩ := eq_mod_one_of_rayAccum_of_angDouble_eq hφ hrep hx' hy'' ⟨m, hm2⟩
      have hb1 : 0 ≤ x ∧ x < 1 := ⟨(hKmem x).mp hx |>.2.1, (hKmem x).mp hx |>.2.2⟩
      have hb2 : 0 ≤ y' ∧ y' < 1 := ⟨(hKmem y').mp hy' |>.2.1, (hKmem y').mp hy' |>.2.2⟩
      have hmmz : mm = 0 := by
        have hlt : (mm : ℝ) < 1 := by linarith [hmm, hb1.2, hb2.2]
        have hgt : (-1 : ℝ) < (mm : ℝ) := by linarith [hmm, hb1.1, hb2.1]
        have hlt' : mm < 1 := by exact_mod_cast hlt
        have hgt' : -1 < mm := by exact_mod_cast hgt
        omega
      rw [hmmz, Int.cast_zero, add_zero] at hmm
      exact hmm
  simpa only [hK, hA] using hfin

/-- The residual gap in Goldberg-Milnor B.1: a ray that lands at a repelling periodic point has a
periodic angle.  If `φ` is a Böttcher coordinate of `T_c`, `y` is a repelling periodic point of odd
period `k` (`Work.Landing.IsRepelling c k y`), and the ray at angle `θ` has accumulating set `{y}`
(`Work.Landing.rayAccum c φ θ = {y}`), then the class of `θ` modulo `1` is periodic under the
angle map. -/
theorem periodicAngle_of_landsAt_isRepelling {c : ℂ} {φ : ℂ → ℂ} {θ : ℝ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    (hland : Work.Landing.rayAccum c φ θ = {y}) :
    ∃ q : ℕ, 0 < q ∧ Work.Landing.PeriodicAngle (Int.fract θ) (2 * k * q) := by
  exact periodicAngle_of_finite_type hφ hrep hland (finite_typeAngles hφ hrep)

end Work.LandLeaves
