import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.centred0_zonoidDiff_seq
import Submission.Commons.Geometry.Convex.Hadwiger.continuous_bodyAdd_left
import Submission.Commons.Geometry.Convex.Hadwiger.zonoidLimit_of_continuous_even_nonneg

/-!
# `zonoidDiff_seq`: centred bodies are limits of differences of zonoids

Klain, *A short proof of Hadwiger's characterization theorem*, Mathematika 42
(1995), Prop. 3.1: every *centred* convex body `K` (symmetric about some point
`v/2`) is a Hausdorff limit of convex bodies `K_j` each of which is a
difference of two zonoids: there are zonoids `Y₁`, `Y₂` — Hausdorff limits of
`[0,1]`-box zonotopes `Zᵢ(n) = {Σ tᵢ • wᵢ : tᵢ ∈ [0,1]}` — with
`K_j + Y₂ = Y₁`.

The origin-symmetric case is the commons lemma
`centred0_zonoidDiff_seq` (the analytic core: smooth-centre density plus the
cosine-transform/Funk--Hecke surjectivity onto even smooth functions).  Here we
reduce the general case to the origin-symmetric one by translating the body so
that its centre becomes the origin, and translating the difference-of-zonoids
representation back using the identity `{a} + [0,-a] = [0,a]` for the
one-dimensional box zonotopes.  All that is needed on the way are

* `boxZono_add_boxZono_one`: adding one box-zonotope generator to the carrier
  of a box zonotope;
* `ptBody_add_segBody_neg`: `{a} + [0, -a] = [0, a]`.

Both are elementary set identities, proved below.
-/

open Set
open scoped Pointwise Topology BigOperators Classical

namespace Commons.Geometry.Convex.Hadwiger

open Filter

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

/-- The single-point convex body `{a}`. -/
def ptBody (a : V) : ConvexBody V :=
  ⟨{a}, convex_singleton a, isCompact_singleton, Set.singleton_nonempty a⟩

@[simp] theorem ptBody_coe (a : V) : (ptBody a : Set V) = {a} := rfl

/-- The segment `[0, a]`, viewed as a box zonotope with a single generator. -/
abbrev segBody (a : V) : ConvexBody V := boxZonoBody 1 (fun _ : Fin 1 => a)

@[simp] theorem segBody_coe (a : V) : (segBody a : Set V) = boxZono 1 (fun _ : Fin 1 => a) := rfl

/-- Adding one generator to a box zonotope:
`boxZono k w + [0,a] = boxZono (k+1) (Fin.cons a w)`. -/
theorem boxZono_add_boxZono_one (k : ℕ) (w : Fin k → V) (a : V) :
    boxZono k w + boxZono 1 (fun _ : Fin 1 => a) = boxZono (k + 1) (Fin.cons a w) := by
  ext x
  rw [Set.mem_add]
  constructor
  · rintro ⟨p, hp, q, hq, hpq⟩
    rw [boxZono_mem_iff] at hp hq
    rcases hp with ⟨t, ht, rfl⟩
    rcases hq with ⟨s, hs, rfl⟩
    rw [boxZono_mem_iff]
    refine ⟨Fin.cons (s 0) t, ?mem, ?sum⟩
    · intro i
      by_cases hi : i = 0
      · subst i
        simpa using hs 0
      · have hsucc := Fin.succ_pred i hi
        rw [← hsucc, Fin.cons_succ]
        exact ht (Fin.pred i hi)
    · rw [← hpq]
      rw [Fin.sum_univ_one, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [add_comm]
  · intro hx
    rw [boxZono_mem_iff] at hx
    rcases hx with ⟨u, hu, rfl⟩
    refine ⟨∑ j : Fin k, u j.succ • w j, ?_, u 0 • a, ?_, ?_⟩
    · rw [boxZono_mem_iff]
      exact ⟨u ∘ Fin.succ, fun j => hu j.succ, rfl⟩
    · rw [boxZono_mem_iff]
      refine ⟨fun _ : Fin 1 => u 0, ?_, ?_⟩
      · intro i
        exact hu 0
      · simp
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [add_comm]

/-- Body-level form of `boxZono_add_boxZono_one`. -/
theorem boxZonoBody_add_segBody (k : ℕ) (w : Fin k → V) (a : V) :
    boxZonoBody k w + segBody a = boxZonoBody (k + 1) (Fin.cons a w) := by
  apply ConvexBody.ext
  rw [ConvexBody.coe_add, boxZonoBody_coe]
  exact boxZono_add_boxZono_one k w a

/-- `{a} + [0,-a] = [0,a]`. -/
theorem ptBody_add_segBody_neg (a : V) : ptBody a + segBody (-a) = segBody a := by
  apply ConvexBody.ext
  show ({a} : Set V) + boxZono 1 (fun _ : Fin 1 => -a) = boxZono 1 (fun _ : Fin 1 => a)
  ext x
  rw [Set.mem_add]
  constructor
  · rintro ⟨p, hp, q, hq, hpq⟩
    rw [Set.mem_singleton_iff] at hp
    subst hp
    rw [boxZono_mem_iff] at hq
    rcases hq with ⟨t, ht, rfl⟩
    rw [boxZono_mem_iff]
    refine ⟨fun _ : Fin 1 => 1 - t 0, ?_, ?_⟩
    · intro i
      fin_cases i
      exact ⟨by linarith [(ht 0).2], by linarith [(ht 0).1]⟩
    · rw [Fin.sum_univ_one] at hpq ⊢
      rw [← hpq]
      rw [smul_neg, ← sub_eq_add_neg, sub_smul, one_smul]
  · intro hx
    rw [boxZono_mem_iff] at hx
    rcases hx with ⟨s, hs, hxs⟩
    refine ⟨a, ?_, (1 - s 0) • (-a), ?_, ?_⟩
    · rw [Set.mem_singleton_iff]
    · rw [boxZono_mem_iff]
      refine ⟨fun _ : Fin 1 => 1 - s 0, ?_, ?_⟩
      · intro i
        fin_cases i
        exact ⟨by linarith [(hs 0).2], by linarith [(hs 0).1]⟩
      · rw [Fin.sum_univ_one]
    · rw [Fin.sum_univ_one] at hxs
      rw [hxs]
      rw [smul_neg, ← sub_eq_add_neg, sub_smul, one_smul]
      abel

/-- **Main lemma.**  A centred convex body is a Hausdorff limit of differences
of two zonoids (each a limit of `[0,1]`-box zonotopes). -/
theorem zonoidDiff_seq
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] (K : ConvexBody V)
    (hK : ∃ v : V, (K : Set V) = (fun x : V => -x + v) '' (K : Set V)) :
    ∃ Kj : ℕ → ConvexBody V,
      Tendsto Kj atTop (𝓝 K) ∧
      ∀ j : ℕ, ∃ (Y₁ Y₂ : ConvexBody V) (Z₁ Z₂ : ℕ → ConvexBody V)
        (k₁ k₂ : ℕ → ℕ) (w₁ : ∀ n : ℕ, Fin (k₁ n) → V) (w₂ : ∀ n : ℕ, Fin (k₂ n) → V),
        Tendsto Z₁ atTop (𝓝 Y₁) ∧ Tendsto Z₂ atTop (𝓝 Y₂) ∧
        (∀ n : ℕ, (Z₁ n : Set V) =
          {x : V | ∃ t : Fin (k₁ n) → ℝ, (∀ i : Fin (k₁ n), t i ∈ Set.Icc (0 : ℝ) 1) ∧
            x = ∑ i : Fin (k₁ n), t i • w₁ n i}) ∧
        (∀ n : ℕ, (Z₂ n : Set V) =
          {x : V | ∃ t : Fin (k₂ n) → ℝ, (∀ i : Fin (k₂ n), t i ∈ Set.Icc (0 : ℝ) 1) ∧
            x = ∑ i : Fin (k₂ n), t i • w₂ n i}) ∧
        Kj j + Y₂ = Y₁ := by
  classical
  rcases hK with ⟨v, hv⟩
  set c : V := (1/2 : ℝ) • v with hc
  have hc2 : (2 : ℝ) • c = v := by
    rw [hc, smul_smul]
    norm_num
  -- symmetry of `K` about `c`: `k ∈ K → 2c - k ∈ K`
  have hsymK : ∀ k ∈ (K : Set V), (2 : ℝ) • c - k ∈ (K : Set V) := by
    intro k hk
    have hmem : (-k + v) ∈ (K : Set V) := by
      rw [hv]
      exact ⟨k, hk, rfl⟩
    have : -k + v = (2 : ℝ) • c - k := by
      rw [hc2]; abel
    rwa [this] at hmem
  have key : ∀ k : V, (2 : ℝ) • c - k + (-c) = -(k + (-c)) := by
    intro k
    rw [show (2 : ℝ) = 1 + 1 by norm_num, add_smul, one_smul]
    abel
  let K0 : ConvexBody V := K + ptBody (-c)
  have hsym : (K0 : Set V) = -(K0 : Set V) := by
    show (K : Set V) + {(-c)} = -((K : Set V) + {(-c)})
    ext y
    constructor
    · intro hy
      rw [Set.mem_add] at hy
      rcases hy with ⟨k, hk, w, hw, hkw⟩
      rw [Set.mem_singleton_iff] at hw
      subst hw
      rw [Set.mem_neg, Set.mem_add]
      refine ⟨(2 : ℝ) • c - k, hsymK k hk, -c, by rw [Set.mem_singleton_iff], ?_⟩
      rw [← hkw]
      exact key k
    · intro hy
      rw [Set.mem_neg, Set.mem_add] at hy
      rcases hy with ⟨k, hk, w, hw, hkw⟩
      rw [Set.mem_singleton_iff] at hw
      subst hw
      rw [Set.mem_add]
      refine ⟨(2 : ℝ) • c - k, hsymK k hk, -c, by rw [Set.mem_singleton_iff], ?_⟩
      have hy' : y = -(k + (-c)) := by
        have h : -(k + (-c)) = -(-y) := congrArg Neg.neg hkw
        simpa using h.symm
      rw [hy']
      exact key k
  rcases centred0_zonoidDiff_seq V K0 hsym with ⟨X, hXconv, hXdata⟩
  refine ⟨fun j => X j + ptBody c, ?_, ?_⟩
  · have htend : Tendsto (fun j : ℕ => X j + ptBody c) atTop (𝓝 (K0 + ptBody c)) :=
      (continuous_bodyAdd_left (ptBody c)).continuousAt.tendsto.comp hXconv
    have hK0c : K0 + ptBody c = K := by
      apply ConvexBody.ext
      show ((K : Set V) + {(-c)}) + {c} = (K : Set V)
      ext y
      constructor
      · intro hy
        rw [Set.mem_add] at hy
        rcases hy with ⟨z, hz, w, hw, hzw⟩
        rw [Set.mem_singleton_iff] at hw
        subst hw
        rw [Set.mem_add] at hz
        rcases hz with ⟨k, hk, u, hu, hku⟩
        rw [Set.mem_singleton_iff] at hu
        subst hu
        have hyk : y = k := by
          rw [← hzw, ← hku]
          abel
        rwa [hyk]
      · intro hy
        rw [Set.mem_add]
        refine ⟨y + (-c), ?_, c, by rw [Set.mem_singleton_iff], ?_⟩
        · rw [Set.mem_add]
          exact ⟨y, hy, -c, by rw [Set.mem_singleton_iff], rfl⟩
        · abel
    rwa [hK0c] at htend
  · intro j
    rcases hXdata j with ⟨Y₁, Y₂, Z₁, Z₂, k₁, k₂, w₁, w₂, hT1, hT2, hc1, hc2, heq⟩
    refine ⟨Y₁ + segBody c, Y₂ + segBody (-c),
            (fun n => Z₁ n + segBody c), (fun n => Z₂ n + segBody (-c)),
            (fun n => k₁ n + 1), (fun n => k₂ n + 1),
            (fun n => Fin.cons c (w₁ n)), (fun n => Fin.cons (-c) (w₂ n)),
            ?_, ?_, ?_, ?_, ?_⟩
    · exact (continuous_bodyAdd_left (segBody c)).continuousAt.tendsto.comp hT1
    · exact (continuous_bodyAdd_left (segBody (-c))).continuousAt.tendsto.comp hT2
    · intro n
      rw [ConvexBody.coe_add, hc1 n, ← boxZono_eq_set (k₁ n) (w₁ n), segBody_coe,
        boxZono_add_boxZono_one, boxZono_eq_set]
    · intro n
      rw [ConvexBody.coe_add, hc2 n, ← boxZono_eq_set (k₂ n) (w₂ n), segBody_coe,
        boxZono_add_boxZono_one, boxZono_eq_set]
    · have hpt := ptBody_add_segBody_neg c
      have hsplit : (X j + ptBody c) + (Y₂ + segBody (-c)) =
          (X j + Y₂) + (ptBody c + segBody (-c)) := by ac_rfl
      rw [hsplit, heq, hpt]

end

end Commons.Geometry.Convex.Hadwiger
