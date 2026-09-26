import Mathlib
import Submission.Work.CoreTopology.Disk

/-!
# Intersection lower bound for simple curves on the standard torus

The main result of this file, `min_le_encard_inter_standardCurve`, is the geometric
input `IntersectionLowerBound` needed to compute Pardon's invariant `I(F, β)` for the
standard torus of revolution and the standard `(p,q)`-curve.

The two ingredients are proved here:

* `mem_range_standardCurve_iff_aux`: a point `torusMap u v` of the standard torus lies
  on the standard `(p,q)`-curve if and only if `p v - q u ∈ 2πℤ`.  This is the
  combination of `Work.Core.torusMap_eq_iff` (membership means equality modulo `2π`
  in both coordinates) with Bézout's identity for the coprime integers `p`, `q`.
* `encard_shift_mul_two_pi_aux`: if a continuous function `f : ℝ → ℝ` satisfies
  `f (2π) = f 0 + N·2π`, then `f` meets the lattice `2πℤ` in at least `|N|` points of
  the half-open fundamental period `[0, 2π)`.  Indeed an interval of length `2π|N|`
  contains at least `|N|` lattice points, and the intermediate value theorem realises
  each of them strictly below `f (2π)`, hence at a parameter in `[0, 2π)`.

Putting these together for `Ψ t = p Φ t - q Θ t` (where `(Θ, Φ)` is a lift of `α`) gives
the counting argument described in the statement below.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.CoreTopology

noncomputable section

/-- **Counting lattice points of `2πℤ` met by a function on one period (positive case).**
If `f` is continuous and `f (2π) = f 0 + N·2π` with `N ≥ 1`, then `f` takes values in
`2πℤ` at at least `N` points of the fundamental period `[0, 2π)`.

The multiples of `2π` occurring in the interval `[f 0, f (2π))` are
`2π·(⌈f 0 / 2π⌉ + k)` for `k = 0, …, N-1`; all of them lie strictly below
`f (2π)`, so the intermediate value theorem produces parameters in `[0, 2π)` at which
`f` attains them, and these parameters are pairwise distinct. -/
private lemma encard_shift_mul_two_pi_aux_pos (f : ℝ → ℝ) (hf : Continuous f) (N : ℤ)
    (hN : 1 ≤ N) (hshift : f (2 * Real.pi) = f 0 + (N : ℝ) * (2 * Real.pi)) :
    (N.natAbs : ENat) ≤ Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      ∃ m : ℤ, f t = (m : ℝ) * (2 * Real.pi)} := by
  have hπ : (0:ℝ) < 2 * Real.pi := Real.two_pi_pos
  set c : ℝ := f 0 with hcdef
  set K : ℤ := ⌈c / (2 * Real.pi)⌉ with hKdef
  have hK1 : c ≤ (K : ℝ) * (2 * Real.pi) := by
    have h := Int.le_ceil (c / (2 * Real.pi))
    have h' : c / (2 * Real.pi) * (2 * Real.pi) ≤ (K : ℝ) * (2 * Real.pi) := by
      rw [hKdef]; exact mul_le_mul_of_nonneg_right h (le_of_lt hπ)
    rwa [div_mul_cancel₀ c (ne_of_gt hπ)] at h'
  have hK2 : (K : ℝ) < c / (2 * Real.pi) + 1 := by
    rw [hKdef]; exact Int.ceil_lt_add_one _
  have hcast : ∀ k : ℕ, (((K + (k:ℤ)) : ℤ) : ℝ) = (K:ℝ) + (k:ℝ) := by
    intro k; push_cast; ring
  have hchoose : ∀ k : ℕ, k < N.natAbs →
      ∃ t : ℝ, t ∈ Set.Ico (0:ℝ) (2 * Real.pi) ∧
        f t = (((K + (k : ℤ)) : ℤ) : ℝ) * (2 * Real.pi) := by
    intro k hk
    have hkN : (1:ℝ) + (k:ℝ) ≤ (N:ℝ) := by
      have hk1 : (k : ℤ) < N := by
        have h : (k : ℤ) < (N.natAbs : ℤ) := by exact_mod_cast hk
        rwa [Int.natAbs_of_nonneg (by omega : (0:ℤ) ≤ N)] at h
      have h : ((k:ℤ) + 1 : ℤ) ≤ N := by omega
      have h' : (((k:ℤ) + 1 : ℤ) : ℝ) ≤ (N:ℝ) := by exact_mod_cast h
      have h2 : (((k:ℤ) + 1 : ℤ) : ℝ) = (k:ℝ) + 1 := by push_cast; ring
      linarith [h', h2.le, h2.ge]
    have hy_ge : f 0 ≤ ((K:ℝ) + (k:ℝ)) * (2*Real.pi) := by
      have hle : (K:ℝ) ≤ (K:ℝ) + (k:ℝ) := by
        have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        linarith
      calc f 0 = c := hcdef.symm
        _ ≤ (K : ℝ) * (2*Real.pi) := hK1
        _ ≤ _ := mul_le_mul_of_nonneg_right hle (le_of_lt hπ)
    have hy_lt : ((K:ℝ) + (k:ℝ)) * (2*Real.pi) < f (2*Real.pi) := by
      have hstep : ((K:ℝ) + (k:ℝ)) * (2*Real.pi) <
          (c / (2*Real.pi) + 1 + (k:ℝ)) * (2*Real.pi) := by
        apply mul_lt_mul_of_pos_right _ hπ
        linarith [hK2]
      have h2 : (c / (2*Real.pi) + 1 + (k:ℝ)) * (2*Real.pi) ≤
          c + (N:ℝ)*(2*Real.pi) := by
        have h4 : c / (2*Real.pi) + 1 + (k:ℝ) ≤ c/(2*Real.pi) + (N:ℝ) := by linarith
        have h5 := mul_le_mul_of_nonneg_right h4 (le_of_lt hπ)
        have e1 : (c / (2*Real.pi) + 1 + (k:ℝ)) * (2*Real.pi)
            = c + (1 + (k:ℝ)) * (2*Real.pi) := by
          rw [add_mul, add_mul, div_mul_cancel₀ c (ne_of_gt hπ)]; ring
        have e2 : (c / (2*Real.pi) + (N:ℝ)) * (2*Real.pi)
            = c + (N:ℝ) * (2*Real.pi) := by
          rw [add_mul, div_mul_cancel₀ c (ne_of_gt hπ)]
        rw [e1, e2] at h5
        linarith [h5]
      rw [hshift]
      linarith [hstep, h2]
    have hy_mem : ((K:ℝ) + (k:ℝ)) * (2*Real.pi) ∈ Set.Icc (f 0) (f (2*Real.pi)) :=
      ⟨hy_ge, le_of_lt hy_lt⟩
    have hsub := intermediate_value_Icc (a := (0:ℝ)) (b := 2 * Real.pi)
      (le_of_lt hπ) hf.continuousOn
    obtain ⟨t, ht, hft⟩ := hsub hy_mem
    have hlt : t < 2 * Real.pi := by
      rcases lt_or_eq_of_le ht.2 with h | h
      · exact h
      · exfalso
        have : f t = f (2*Real.pi) := by rw [h]
        rw [hft] at this
        linarith [hy_lt]
    exact ⟨t, ⟨ht.1, hlt⟩, by rw [hcast k]; exact hft⟩
  set τ : ℕ → ℝ := fun k => if hk : k < N.natAbs then (hchoose k hk).choose else 0
    with hτdef
  have hτspec : ∀ k (hk : k < N.natAbs), τ k ∈ Set.Ico 0 (2*Real.pi) ∧
      f (τ k) = (((K + (k:ℤ)) : ℤ) : ℝ) * (2*Real.pi) := by
    intro k hk
    rw [hτdef]
    simp only [dif_pos hk]
    exact (hchoose k hk).choose_spec
  have hinj : Set.InjOn τ ↑(Finset.range N.natAbs) := by
    intro a ha b hb hab
    have ha' : a < N.natAbs := Finset.mem_range.mp ha
    have hb' : b < N.natAbs := Finset.mem_range.mp hb
    have hfa := (hτspec a ha').2
    have hfb := (hτspec b hb').2
    rw [hab] at hfa
    have hkey : (((K + (a:ℤ)) : ℤ) : ℝ) = (((K + (b:ℤ)) : ℤ) : ℝ) :=
      mul_right_cancel₀ (ne_of_gt hπ) (by rw [← hfa, hfb])
    have : (K + (a:ℤ) : ℤ) = (K + (b:ℤ) : ℤ) := by exact_mod_cast hkey
    omega
  have hcard : ((Finset.range N.natAbs).image τ).card = N.natAbs := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hsub : (↑((Finset.range N.natAbs).image τ) : Set ℝ) ⊆
      {t : ℝ | t ∈ Set.Ico 0 (2*Real.pi) ∧ ∃ m : ℤ, f t = (m : ℝ) * (2 * Real.pi)} := by
    intro t ht
    rw [Finset.mem_coe, Finset.mem_image] at ht
    obtain ⟨k, hk, rfl⟩ := ht
    exact ⟨(hτspec k (Finset.mem_range.mp hk)).1, K + (k:ℤ),
      (hτspec k (Finset.mem_range.mp hk)).2⟩
  calc (N.natAbs : ENat) = ((↑((Finset.range N.natAbs).image τ) : Set ℝ)).encard := by
        rw [Set.encard_coe_eq_coe_finsetCard, hcard]
    _ ≤ _ := Set.encard_le_encard hsub

/-- **Counting lattice points of `2πℤ` met by a function on one period.**
If `f : ℝ → ℝ` is continuous and `f (2π) = f 0 + N·2π`, then `f` takes a value in `2πℤ`
at at least `|N|` points of the fundamental period `[0, 2π)`.

For `N ≥ 1` this is `encard_shift_mul_two_pi_aux_pos`; for `N ≤ -1` it is applied to
`-f`, whose shift is `-N·2π` and which meets `2πℤ` at exactly the same points. -/
private lemma encard_shift_mul_two_pi_aux (f : ℝ → ℝ) (hf : Continuous f) (N : ℤ)
    (hshift : f (2 * Real.pi) = f 0 + (N : ℝ) * (2 * Real.pi)) :
    (N.natAbs : ENat) ≤ Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      ∃ m : ℤ, f t = (m : ℝ) * (2 * Real.pi)} := by
  rcases lt_trichotomy N 0 with hN | hN | hN
  · have hN1 : (1:ℤ) ≤ -N := by omega
    have hshift' : (fun t : ℝ => -f t) (2*Real.pi) =
        (fun t : ℝ => -f t) 0 + ((-N : ℤ) : ℝ) * (2*Real.pi) := by
      simp only [hshift]; push_cast; ring
    have hmain := encard_shift_mul_two_pi_aux_pos (fun t : ℝ => -f t) hf.neg (-N) hN1 hshift'
    have hset : {t : ℝ | t ∈ Set.Ico 0 (2*Real.pi) ∧ ∃ m : ℤ, -f t = (m:ℝ)*(2*Real.pi)}
        = {t : ℝ | t ∈ Set.Ico 0 (2*Real.pi) ∧ ∃ m : ℤ, f t = (m:ℝ)*(2*Real.pi)} := by
      ext t; constructor
      · rintro ⟨h1, m, hm⟩
        exact ⟨h1, -m, by push_cast; linarith⟩
      · rintro ⟨h1, m, hm⟩
        exact ⟨h1, -m, by push_cast; linarith⟩
    rw [hset] at hmain
    rwa [Int.natAbs_neg] at hmain
  · rw [hN]; simp
  · exact encard_shift_mul_two_pi_aux_pos f hf N (by omega) hshift

/-- **Membership in the standard `(p,q)`-curve in terms of the two angles.**
A point `torusMap u v` of the standard torus lies on the standard `(p,q)`-curve
`t ↦ torusMap (p t) (q t)` if and only if `p v - q u` is an integer multiple of `2π`.

By `Work.Core.torusMap_eq_iff`, membership means that `u ≡ p t` and `v ≡ q t`
modulo `2π` for some `t`, which forces `p v - q u ≡ 0`; conversely, if
`p v - q u = 2π m` then `t = x u + y v`, where `x p + y q = 1` is Bézout's identity
for the coprime integers `p` and `q`, satisfies `p t ≡ u` and `q t ≡ v` modulo `2π`. -/
private lemma mem_range_standardCurve_iff_aux (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q)
    (hc : Nat.Coprime p q) (u v : ℝ) :
    Work.Core.torusMap u v ∈ Set.range (standardCurve p q).γ ↔
      ∃ m : ℤ, (p : ℝ) * v - (q : ℝ) * u = (m : ℝ) * (2 * Real.pi) := by
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ, x * (p:ℤ) + y * (q:ℤ) = 1 := by
    refine ⟨Nat.gcdA p q, Nat.gcdB p q, ?_⟩
    have h := Nat.gcd_eq_gcd_ab p q
    rw [hc] at h
    push_cast at h ⊢
    linarith [h]
  constructor
  · rintro ⟨s, hs⟩
    have hs' : Work.Core.torusMap ((p:ℝ)*s) ((q:ℝ)*s) = Work.Core.torusMap u v := hs
    obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ :=
      (Work.Core.torusMap_eq_iff ((p:ℝ)*s) ((q:ℝ)*s) u v).mp hs'
    have hu : u = (p:ℝ)*s - (k:ℝ)*(2*Real.pi) := by linarith [hk]
    have hv : v = (q:ℝ)*s - (l:ℝ)*(2*Real.pi) := by linarith [hl]
    exact ⟨(q:ℤ)*k - (p:ℤ)*l, by rw [hu, hv]; push_cast; ring⟩
  · rintro ⟨m, hm⟩
    refine ⟨(x:ℝ)*u + (y:ℝ)*v, ?_⟩
    show Work.Core.torusMap ((p:ℝ)*((x:ℝ)*u + (y:ℝ)*v)) ((q:ℝ)*((x:ℝ)*u + (y:ℝ)*v)) =
      Work.Core.torusMap u v
    rw [Work.Core.torusMap_eq_iff]
    have hxy' : (x:ℝ) * (p:ℝ) + (y:ℝ) * (q:ℝ) = 1 := by
      have h2 : ((x * (p:ℤ) + y * (q:ℤ) : ℤ) : ℝ) = 1 := by rw [hxy]; norm_num
      push_cast at h2; linarith [h2]
    refine ⟨⟨y*m, ?_⟩, ⟨-(x*m), ?_⟩⟩
    · push_cast
      linear_combination (↑y : ℝ) * hm + u * hxy'
    · push_cast
      linear_combination -(↑x : ℝ) * hm + v * hxy'

/-- **Intersection lower bound for simple curves on the standard torus.** Let `p, q > 0` be coprime, `α` a simple closed curve on the standard torus of revolution, and `L` a lift of `α` whose winding vector `(a, b) = L.winding` is nonzero and has `a = 0` or `b = 0`. Then `α` meets the standard `(p,q)`-curve in at least `min p q` points.

Reduction: a point `α t = torusMap (Θ t) (Φ t)` of the curve lies on the `(p,q)` curve `s ↦ torusMap (p s) (q s)` exactly when `∃ s, Θ t ≡ p s (mod 2π) ∧ Φ t ≡ q s (mod 2π)`, which (using `Nat.Coprime p q` and `p, q > 0`) is equivalent to `p Φ t - q Θ t ∈ 2πℤ`. The continuous function `Ψ t = p Φ t - q Θ t` satisfies `Ψ (2π) - Ψ 0 = 2π (p b - q a)`, whose absolute value is `2π · max (p |b|) (q |a|) ≥ 2π · min p q`; by the intermediate value theorem `Ψ` therefore takes at least `|p b - q a| ≥ min p q` values in `2πℤ` on one period, and simplicity of `α` on `[0, 2π)` (i.e. `IsSimple standard α`) converts these into that many distinct intersection points. -/
theorem min_le_encard_inter_standardCurve (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (α : ClosedCurve standard) (hsimple : IsSimple standard α)
    (L : LiftOf standard α) (hne : L.winding ≠ (0, 0))
    (hdich : (L.winding).1 = 0 ∨ (L.winding).2 = 0) :
    (Nat.min p q : ℕ∞) ≤ Set.encard (Set.range α.γ ∩ Set.range (standardCurve p q).γ) := by
  set Ψ : ℝ → ℝ := fun t => (p : ℝ) * L.Φ t - (q : ℝ) * L.Θ t with hΨdef
  have hΨcont : Continuous Ψ := by
    rw [hΨdef]
    exact (continuous_const.mul L.contΦ).sub (continuous_const.mul L.contΘ)
  set N : ℤ := (p : ℤ) * (L.winding).2 - (q : ℤ) * (L.winding).1 with hNdef
  have hshift : Ψ (2 * Real.pi) = Ψ 0 + (N : ℝ) * (2 * Real.pi) := by
    simp only [hΨdef, hNdef, (L.winding_spec).2, (L.winding_spec).1]
    push_cast
    ring
  set S : Set ℝ := {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
    ∃ m : ℤ, Ψ t = (m : ℝ) * (2 * Real.pi)} with hS
  have hSbound : (N.natAbs : ℕ∞) ≤ S.encard := by
    rw [hS]; exact encard_shift_mul_two_pi_aux Ψ hΨcont N hshift
  have hNge : (Nat.min p q : ℕ∞) ≤ (N.natAbs : ℕ∞) := by
    rcases hdich with ha | hb
    · have hbne : (L.winding).2 ≠ 0 := by
        intro h; exact hne (Prod.ext ha h)
      have hN : N = (p : ℤ) * (L.winding).2 := by rw [hNdef, ha]; ring
      have hNabs : N.natAbs = p * (L.winding).2.natAbs := by
        rw [hN, Int.natAbs_mul]
        simp
      rw [hNabs]
      have hb1 : 1 ≤ (L.winding).2.natAbs := Int.natAbs_pos.mpr hbne
      have key : Nat.min p q ≤ p * (L.winding).2.natAbs := by
        calc Nat.min p q ≤ p := Nat.min_le_left _ _
          _ = p * 1 := (Nat.mul_one p).symm
          _ ≤ p * (L.winding).2.natAbs := Nat.mul_le_mul_left p hb1
      exact_mod_cast key
    · have hane : (L.winding).1 ≠ 0 := by
        intro h; exact hne (Prod.ext h hb)
      have hN : N = -((q : ℤ) * (L.winding).1) := by rw [hNdef, hb]; ring
      have hNabs : N.natAbs = q * (L.winding).1.natAbs := by
        rw [hN, Int.natAbs_neg, Int.natAbs_mul]
        simp
      rw [hNabs]
      have ha1 : 1 ≤ (L.winding).1.natAbs := Int.natAbs_pos.mpr hane
      have key : Nat.min p q ≤ q * (L.winding).1.natAbs := by
        calc Nat.min p q ≤ q := Nat.min_le_right _ _
          _ = q * 1 := (Nat.mul_one q).symm
          _ ≤ q * (L.winding).1.natAbs := Nat.mul_le_mul_left q ha1
      exact_mod_cast key
  have himg : α.γ '' S ⊆ Set.range α.γ ∩ Set.range (standardCurve p q).γ := by
    rintro y ⟨t, ht, rfl⟩
    refine ⟨⟨t, rfl⟩, ?_⟩
    rw [hS] at ht
    obtain ⟨m, hm⟩ := ht.2
    have hm' : (p : ℝ) * L.Φ t - (q : ℝ) * L.Θ t = (m : ℝ) * (2 * Real.pi) := by
      simpa only [hΨdef] using hm
    have hmem : Work.Core.torusMap (L.Θ t) (L.Φ t) ∈ Set.range (standardCurve p q).γ :=
      (mem_range_standardCurve_iff_aux p q hp hq hc (L.Θ t) (L.Φ t)).mpr ⟨m, hm'⟩
    rw [← L.lifts t]
    simpa only [standard_psi] using hmem
  have hencard : (α.γ '' S).encard = S.encard :=
    (hsimple.mono (fun t ht => ht.1)).encard_image
  calc (Nat.min p q : ℕ∞) ≤ (N.natAbs : ℕ∞) := hNge
    _ ≤ S.encard := hSbound
    _ = (α.γ '' S).encard := hencard.symm
    _ ≤ Set.encard (Set.range α.γ ∩ Set.range (standardCurve p q).γ) :=
        Set.encard_le_encard himg

end

end Work.CoreTopology
