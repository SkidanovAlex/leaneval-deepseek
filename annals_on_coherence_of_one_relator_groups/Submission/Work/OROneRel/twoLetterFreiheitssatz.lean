import Mathlib
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.winAssembly
import Submission.Work.OROneRel.twoLetter_cycle_decor
import Submission.Work.OROneRel.lsig_wordOf_eq_zero
import Submission.Work.OROneRel.twoLetterWindow_neg
import Submission.Work.OROneRel.twoLetterFreiheitssatz_neg_of_pos
import Submission.Work.OROneRel.levelChain
import Submission.Work.OROneRel.normalClosure_step
import Submission.Work.OROneRel.decor_tlU_tlW_at
import Submission.Work.OROneRel.walkWord_step_up
import Submission.Work.OROneRel.walkWord_step_down
import Submission.Work.OROneRel.ker_gaugeMap_le_winTree
import Submission.Work.OROneRel.normalClosure_finite_subset
import Submission.Work.OROneRel.mem_normalClosure_singleton
import Submission.Work.OROneRel.WrelUp_supported
import Submission.Work.OROneRel.WrelDown_supported
import Submission.Work.OROneRel.twoLetterFreiheitssatz_global
import Submission.Work.OROneRel.betaCast_spec

namespace Work.OROneRel

/-!
# The two-letter Freiheitssatz of the domain

The target `Work.OROneRel.twoLetterFreiheitssatz` is the Freiheitssatz of the `ℤ`-domain of the
one-relator group `G = ⟨a, b | (a ^ p * b ^ q) ^ l⟩` (`p, q ≥ 1` coprime, `l ≥ 1`): the class map
`winRho : F (β) →* F 2` of the non-tree edges of the band window sends the preimage of the normal
closure of `u ^ l = (a ^ p * b ^ q) ^ l` into the normal closure of the deleted walk word `winRoot`.

Equivalently, writing `D` for the band window complex (`lo = 0`, `hi = pq`) and `Y` for the `ℤ`-cover
of the presentation complex of `G`, the statement says that the inclusion `D ↪ Y` induces an
injection `π₁(D) ↪ π₁(Y)` (because `π₁(Y) ↪ π₁(X) = G` is `π₁` of a covering, and
`π₁(D) = F (β) / ⟪winRoot ^ l⟫`).

## The two reductions proved below

* `c_eq_tlW_or`: the hypotheses `hcu` (the weight kills `u`) and `hτ` (the weight is surjective) with
  `Nat.Coprime p q` force `c = tlW p q` or `c = -tlW p q`; so the walk of `u` is the staircase
  `0, q, 2q, …, pq, pq - p, …, 0` (or its mirror).
* `decor_tlU_tlW`, `walk_levels_tlW`, `walk_src_zero_tlW`, `walk_tgt_top_tlW`,
  `window_eq_band_tlW`: the decorated walk is the explicit staircase, it stays in `[0, pq]` and
  attains both ends, hence (with `hwin` and `hone`) the window *is* the band `[0, pq]`.
  `Submission.Work.OROneRel.twoLetterWindow_neg` is the mirror statement for `c = -tlW p q`.

## The remaining content, and how it is organised

The gap is Linton's graph-of-spaces splitting (*One-relator hierarchies*, arXiv 2202.11324,
Prop. 2.2.19) for the line of window domains.  The formalisation route is:

1. `Submission.Work.OROneRel.unionAmalgam_injective` (delegated): the atomic van Kampen step --
   `π₁` of one piece of a union of two `2`-complexes injects into `π₁` of the union, provided the two
   amalgamating maps are injective.  This is `presentedGroup_union_amalgam` followed by Mathlib's
   `Monoid.PushoutI.of_injective`.
2. The line amalgam: `Y_N = D_0 ∪ t D_0 ∪ ⋯ ∪ t ^ N D_0` is a chain glued along the gates
   `D_k ∩ D_{k+1}`, so iterating (1) gives `π₁(D_0) ↪ π₁(Y_N)` as soon as each gate's `π₁` injects
   into the two domains it bounds.
3. The gate injection is the *Magnus Freiheitssatz* `Work.OROneRel.freiheitssatz_at` applied to the
   one-relator complex `D_k` with the gate as a Magnus subgraph: it holds as soon as the walk of `D_k`
   is not supported on the gate's generators, which is arranged by an appropriate choice of the
   spanning trees of the domains (the trees must agree on the gates).
4. `F (β) / ⟪winRoot ^ l⟫ ≅ π₁(D_0)` is `Work.OROneRel.presentedGroup_treeDelete_iso` together with
   `Work.OROneRel.winRho_winRoot`.
5. Finally `⟪u ^ l⟫_{F 2} ∩ ker (cohom c) = ⟪σ ^ k (u ^ l) : k ∈ ℤ⟫`, and any element of `F (β)`
   lying in that normal closure uses only finitely many of the shifted relators, hence lies in the
   kernel of `F (β) → π₁(Y_N)` for `N` large, where (2) makes it trivial.
-/

/-!
# The weight killing the two-letter relator

The hypotheses `hcu` (the weight kills `u = a ^ p * b ^ q`) and `hτ` (the weight is surjective,
witnessed by `τ`) force the weight to be, up to sign, the standard one `a ↦ q`, `b ↦ -p`.  This is
the first structural reduction of `Work.OROneRel.twoLetterFreiheitssatz`: it pins down the level
graph of the `ℤ`-cover, hence the shape of the walk of `u`.
-/

/-- **The weight of the two-letter case is `±(q, -p)`.**  For `p, q ≥ 1` coprime and a weight `c`
with `cohom c (a ^ p * b ^ q) = 1` and surjective (i.e. some `τ` has `cohom c τ = ofAdd 1`), we have
`(c 0, c 1) = (q, -p)` or `(c 0, c 1) = (-q, p)`. -/
theorem c_eq_tlW_or (p q : ℕ) (hcop : Nat.Coprime p q)
    {c : Fin 2 → ℤ} {τ : FreeGroup (Fin 2)}
    (hcu : cohom c (tlU p q) = 1) (hτ : cohom c τ = Multiplicative.ofAdd 1) :
    (c 0 = (q : ℤ) ∧ c 1 = -(p : ℤ)) ∨ (c 0 = -(q : ℤ) ∧ c 1 = (p : ℤ)) := by
  -- `cohom c (a ^ p * b ^ q) = ofAdd (p * c 0 + q * c 1)`, so `p * c 0 + q * c 1 = 0`.
  have hcu' : (p : ℤ) * c 0 + (q : ℤ) * c 1 = 0 := by
    rw [tlU, map_mul, map_pow, map_pow] at hcu
    simp only [cohom, FreeGroup.lift_apply_of] at hcu
    rw [← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add] at hcu
    have := Multiplicative.ofAdd.injective hcu
    omega
  -- Surjectivity: `cohom c τ = ofAdd (A * c 0 + B * c 1)` for some integers `A, B`.
  have key : ∀ w : FreeGroup (Fin 2),
      ∃ A B : ℤ, cohom c w = Multiplicative.ofAdd (A * c 0 + B * c 1) := by
    intro w
    induction w using FreeGroup.induction_on with
    | one => exact ⟨0, 0, by simp⟩
    | of i =>
      fin_cases i
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
    | inv_of a ih =>
      obtain ⟨A, B, hAB⟩ := ih
      refine ⟨-A, -B, ?_⟩
      rw [map_inv, hAB, ← ofAdd_neg]
      congr 1
      ring
    | mul a b iha ihb =>
      obtain ⟨A, B, hAB⟩ := iha
      obtain ⟨A', B', hA'B'⟩ := ihb
      refine ⟨A + A', B + B', ?_⟩
      rw [map_mul, hAB, hA'B', ← ofAdd_add]
      congr 1
      ring
  obtain ⟨A, B, hAB⟩ := key τ
  have hAB1 : A * c 0 + B * c 1 = 1 := by
    have h := hAB
    rw [hτ] at h
    exact Multiplicative.ofAdd.injective h.symm
  -- Eliminate: the determinant `d = A * q - B * p` divides both `q` and `p`.
  set d : ℤ := A * (q : ℤ) - B * (p : ℤ) with hd
  have hd0 : d * c 0 = (q : ℤ) := by
    have h : (q : ℤ) * (A * c 0 + B * c 1) - B * ((p : ℤ) * c 0 + (q : ℤ) * c 1)
        = d * c 0 := by rw [hd]; ring
    rw [hAB1, hcu'] at h
    simpa using h.symm
  have hd1 : d * c 1 = -(p : ℤ) := by
    have h : (p : ℤ) * (A * c 0 + B * c 1) - A * ((p : ℤ) * c 0 + (q : ℤ) * c 1)
        = -d * c 1 := by rw [hd]; ring
    rw [hAB1, hcu'] at h
    linarith
  have hdq : d ∣ (q : ℤ) := ⟨c 0, hd0.symm⟩
  have hdp : d ∣ (p : ℤ) := ⟨-(c 1), by rw [mul_neg, hd1]; ring⟩
  have hcopZ : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  obtain ⟨x, y, hxy⟩ := hcopZ
  have hd1' : d ∣ (1 : ℤ) := by
    have := (hdp.mul_left x).add (hdq.mul_left y)
    rwa [hxy] at this
  have hdpm : d = 1 ∨ d = -1 := by
    obtain ⟨k, hk⟩ := hd1'
    exact Int.eq_one_or_neg_one_of_mul_eq_one hk.symm
  rcases hdpm with h | h
  · left
    constructor
    · simpa [h] using hd0
    · simpa [h] using hd1
  · right
    constructor
    · have := hd0; rw [h] at this; omega
    · have := hd1; rw [h] at this; omega

/-!
# The decorated walk of the two-letter relator

With the weight `tlW p q` (`a ↦ q`, `b ↦ -p`) the walk of `a ^ p * b ^ q` on the levels is the
staircase `0, q, 2q, …, pq, pq - p, …, 0`: the `a`-letters are read at the levels `0, q, …, (p-1)q`
and the `b`-letters at the levels `pq, pq - p, …, p`.  In particular the walk stays in `[0, pq]` and
attains both ends, so (with the band hypothesis `hone`) the window of
`Work.OROneRel.twoLetterFreiheitssatz` is *exactly* the band `[0, pq]`.
-/

/-- **The decorated walk of the two-letter relator.**  For the weight `tlW p q` the decorated word of
`a ^ p * b ^ q` is the staircase described above. -/
theorem decor_tlU_tlW (p q : ℕ) :
    decor (tlW p q) 0 (wordOf (tlU p q))
      = List.ofFn (fun j : Fin p => (((0 : Fin 2), (j : ℤ) * (q : ℤ)), true))
        ++ List.ofFn (fun k : Fin q =>
            (((1 : Fin 2), (p : ℤ) * (q : ℤ) - (k : ℤ) * (p : ℤ)), true)) := by
  have hword : wordOf (tlU p q)
      = List.replicate p ((0 : Fin 2), true) ++ List.replicate q ((1 : Fin 2), true) := by
    rw [tlU]
    exact wordOf_of_pow_mul_of_pow (0 : Fin 2) (1 : Fin 2) (by decide) p q
  rw [hword]
  exact decor_two_letter p q

/-- **The walk of the two-letter relator stays in the band `[0, pq]`.** -/
theorem walk_levels_tlW (p q : ℕ) :
    ∀ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
      0 ≤ e.1.2 ∧ e.1.2 ≤ (p : ℤ) * (q : ℤ) ∧
        0 ≤ e.1.2 + tlW p q e.1.1 ∧ e.1.2 + tlW p q e.1.1 ≤ (p : ℤ) * (q : ℤ) := by
  intro e he
  rw [decor_tlU_tlW] at he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
    have hj : (j : ℤ) + 1 ≤ (p : ℤ) := by
      exact_mod_cast (by have := j.isLt; omega : (j : ℕ) + 1 ≤ p)
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
    have hQ : (0 : ℤ) ≤ (q : ℤ) := by positivity
    rw [show tlW p q (0 : Fin 2) = (q : ℤ) from by simp [tlW]]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp he
    have hk : (k : ℤ) + 1 ≤ (q : ℤ) := by
      exact_mod_cast (by have := k.isLt; omega : (k : ℕ) + 1 ≤ q)
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
    have hP : (0 : ℤ) ≤ (p : ℤ) := by positivity
    rw [show tlW p q (1 : Fin 2) = -(p : ℤ) from by simp [tlW]]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- **The walk attains the bottom level `0`.** -/
theorem walk_src_zero_tlW (p q : ℕ) (hp : 1 ≤ p) :
    ∃ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)), e.1.2 = (0 : ℤ) := by
  refine ⟨(((0 : Fin 2), (0 : ℤ) * (q : ℤ)), true), ?_, by simp⟩
  rw [decor_tlU_tlW]
  exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨⟨0, hp⟩, by simp⟩)

/-- **The walk attains the top level `pq`.** -/
theorem walk_tgt_top_tlW (p q : ℕ) (hp : 1 ≤ p) :
    ∃ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)), e.1.2 + tlW p q e.1.1 = (p : ℤ) * (q : ℤ) := by
  have hcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]; simp
  refine ⟨(((0 : Fin 2), ((p : ℤ) - 1) * (q : ℤ)), true), ?_, ?_⟩
  · rw [decor_tlU_tlW]
    refine List.mem_append_left _ (List.mem_ofFn.mpr ⟨⟨p - 1, by omega⟩, ?_⟩)
    simp only [hcast]
  · show ((p : ℤ) - 1) * (q : ℤ) + tlW p q (0 : Fin 2) = (p : ℤ) * (q : ℤ)
    rw [show tlW p q (0 : Fin 2) = (q : ℤ) from by simp [tlW]]
    ring

/-- **The window of the two-letter Freiheitssatz is the band `[0, pq]`.**  For the weight `tlW p q`,
the hypotheses `hwin` (the walk lies in the window) and `hone` (no non-zero translate of the walk
fits) force `lo = 0` and `hi = pq`. -/
theorem window_eq_band_tlW (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    {lo hi : ℤ}
    (hwin : ∀ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
      coverEdge e ∈ winE (tlW p q) lo hi)
    (hone : ∀ k : ℤ, k ≠ 0 →
      ¬ (∀ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
          lo ≤ e.1.2 + k ∧ lo ≤ e.1.2 + tlW p q e.1.1 + k ∧ e.1.2 + k ≤ hi ∧
            e.1.2 + tlW p q e.1.1 + k ≤ hi)) :
    lo = 0 ∧ hi = (p : ℤ) * (q : ℤ) := by
  -- `hwin` gives `lo ≤ 0`, `0 ≤ hi` (from the bottom of the walk) and `pq ≤ hi` (from its top).
  obtain ⟨e₀, he₀, hsrc₀⟩ := walk_src_zero_tlW p q hp
  obtain ⟨e₁, he₁, htgt₁⟩ := walk_tgt_top_tlW p q hp
  have h1 : lo ≤ 0 ∧ 0 ≤ hi := by
    have h := hwin e₀ he₀
    rw [mem_winE] at h
    simp only [coverEdge] at h
    rw [hsrc₀] at h
    exact ⟨h.1, h.2.1⟩
  have h2 : (p : ℤ) * (q : ℤ) ≤ hi := by
    have h := hwin e₁ he₁
    rw [mem_winE] at h
    simp only [coverEdge] at h
    rw [htgt₁] at h
    exact h.2.2.2
  have hlo : lo = 0 := by
    rcases lt_or_ge lo 0 with hlt | hge
    · exfalso
      refine (hone (-1) (by norm_num)) ?_
      intro e he
      obtain ⟨h0, hle, h3, h4⟩ := walk_levels_tlW p q e he
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    · omega
  have hhi : hi = (p : ℤ) * (q : ℤ) := by
    rcases lt_or_ge ((p : ℤ) * (q : ℤ)) hi with hlt | hge
    · exfalso
      refine (hone 1 (by norm_num)) ?_
      intro e he
      obtain ⟨h0, hle, h3, h4⟩ := walk_levels_tlW p q e he
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    · omega
  exact ⟨hlo, hhi⟩

/-!
# The class map lands in the weight kernel

The loop class `coverClassAt Wt c e = Wt e.2 * x * (Wt (e.2 + c x))⁻¹` of an edge of the level graph
always has weight `0`, i.e. lies in `ker (cohom c)`.  This is the first step of the identification of
`winRho (F β)` with a free factor of `ker (cohom c)`, which is what turns the target statement into
the `π₁`-injectivity of the window domain inside the `ℤ`-cover.
-/

/-- **The loop class of an edge has weight `0`.** -/
theorem cohom_coverClassAt {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i) (e : α × ℤ) :
    cohom c (coverClassAt Wt c e) = 1 := by
  rw [coverClassAt, gaugeMap_of, map_mul, map_mul, map_inv, hcoh, hcoh]
  simp only [cohom, FreeGroup.lift_apply_of]
  rw [← ofAdd_add, ← ofAdd_neg, ← ofAdd_add]
  simp

/-- **`winRho` lands in `ker (cohom c)`.** -/
theorem cohom_winRho {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i)
    (x : FreeGroup (winBeta Wt c lo hi)) :
    cohom c (winRho Wt c lo hi x) = 1 := by
  have key : (cohom c).comp (winRho Wt c lo hi) = 1 := by
    refine FreeGroup.ext_hom _ _ fun e => ?_
    rw [MonoidHom.comp_apply, winRho_of, MonoidHom.one_apply]
    exact cohom_coverClassAt Wt c hcoh e.1
  have := congrArg (fun f : FreeGroup (winBeta Wt c lo hi) →* Multiplicative ℤ => f x) key
  simpa using this

/-!
# The walk words of the level graph

The `ℤ`-cover `Y` of the presentation complex of `⟨α | u ^ l⟩` (for the weight `c`) is the level
graph: vertices `ℤ`, an edge `(x, i) : i → i + c x` for each generator `x` and level `i`, and one
`2`-cell at each level `k`, attached along the *walk* of `u` started at `k`.  The walk word
`walkWord c k u` below is the word in the edge generators `α × ℤ` spelled by that walk; it is the
relator of the `2`-cell at level `k` (raised to its `l`-th power for the relator of `⟨α | u ^ l⟩`).

Its gauge image is `Wt k * u * (Wt k)⁻¹` — the `k`-th *shift* of `u`; in particular the level-`0`
walk word is sent by `winRho` to `u` itself (`winRho_winRoot`).
-/

/-- **The walk word at level `k`**: the word in the edge generators `α × ℤ` spelled by the decorated
walk of `u` started at the level `k`. -/
noncomputable def walkWord {α : Type*} (c : α → ℤ) (k : ℤ) (u : FreeGroup α) : FreeGroup (α × ℤ) :=
  FreeGroup.mk (decor c k (wordOf u))

/-- **The gauge image of the walk word at level `k`** is the `k`-th shift `Wt k * u * (Wt k)⁻¹`
of `u`. -/
theorem gaugeMap_walkWord {α : Type*} [DecidableEq α] (Wt : ℤ → FreeGroup α) (c : α → ℤ)
    {u : FreeGroup α} (hu : cohom c u = 1) (k : ℤ) :
    gaugeMap Wt c (walkWord c k u) = Wt k * u * (Wt k)⁻¹ := by
  rw [walkWord, gauge_decor, mk_wordOf, lsig_wordOf_eq_zero c u hu, add_zero]

/-- **The band case of the two-letter Freiheitssatz.**  This is the whole mathematical content of
`Work.OROneRel.twoLetterFreiheitssatz`: for the weight `tlW p q` (`a ↦ q`, `b ↦ -p`), the band window
`[0, p q]` and a gauge `Wt` satisfying the hypotheses, the class map `winRho` identifies
`F (winBeta)/⟪winRoot ^ l⟫` with a subgroup of `G = ⟨a, b | (a^p b^q)^l⟩`.

Equivalently (`presentedGroup_treeDelete_iso`, and `T₀ = winTree` is a spanning tree of the band graph
by `htree` and `trivial_walk_cycle_false`): the inclusion of the band complex `D` (the window `[0,pq]`
with its single `2`-cell) into the `ℤ`-cover `Y` of the presentation complex of `G` induces an
injection `π₁(D) ↪ π₁(Y)`.  This is Linton's `Z`-domain splitting (arXiv 2202.11324, Prop. 2.2.19 and
Theorem 4.13): the line of window domains `D_i = window [i, i+pq]` glued along the gates
`D_i ∩ D_{i+1} = window [i+1, i+pq]` has `π₁`-injective edge maps (each gate is a Magnus subgraph of
the domino it lies in, because the walk attains the levels `lo`/`hi` of that domino), so
`π₁(D_0)` is the vertex group of an HNN decomposition of `π₁(X) = G`.

The content is *independent of the gauge*: `π₁(D) = F(E₀)/⟪τ ∪ {w₀^l}⟫` for every spanning tree `τ` of
the band graph, so one is free to choose a convenient tree when proving the geometric statement. -/
theorem twoLetterFreiheitssatz_band (p q l : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hl : 1 ≤ l)
    (hcop : Nat.Coprime p q) {Wt : ℤ → FreeGroup (Fin 2)} {τ : FreeGroup (Fin 2)}
    (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hcu : Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Work.OROneRel.tlU p q) = 1)
    (hτ : Work.OROneRel.cohom (Work.OROneRel.tlW p q) τ = Multiplicative.ofAdd 1)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (hone : ∀ k : ℤ, k ≠ 0 →
      ¬ (∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
            (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
          0 ≤ e.1.2 + k ∧ 0 ≤ e.1.2 + Work.OROneRel.tlW p q e.1.1 + k ∧
            e.1.2 + k ≤ (p : ℤ) * (q : ℤ) ∧
            e.1.2 + Work.OROneRel.tlW p q e.1.1 + k ≤ (p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) → ∀ e ∈ Work.OROneRel.decor
        (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0
        ((p : ℤ) * (q : ℤ))) :
    ∀ x : FreeGroup (Work.OROneRel.winBeta Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))),
      Work.OROneRel.winRho Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)) x ∈
          Subgroup.normalClosure ({Work.OROneRel.tlU p q ^ l} : Set (FreeGroup (Fin 2))) →
        x ∈ Subgroup.normalClosure
          ({Work.OROneRel.winRoot Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))
              (Work.OROneRel.tlU p q) ^ l} :
            Set (FreeGroup (Work.OROneRel.winBeta Wt (Work.OROneRel.tlW p q) 0
              ((p : ℤ) * (q : ℤ))))) := by
  -- the abstract link, with the global gauge `gaugeExt p q hq Wt` (which agrees with `Wt` on the band)
  have hglob := twoLetterFreiheitssatz_of_gauge (p := p) (q := q) (l := l) hp hq
    (Wt := Wt) (Wt' := gaugeExt p q hq Wt)
    (hW0' := gaugeExt_zero hW0)
    (hcoh' := cohom_gaugeExt hq hcoh)
    (hwalk' := gaugeExt_hwalk hp hq hW0 hcoh htree)
    (hband := fun e he => coverClassAt_gaugeExt_of_band he)
    (hbgt := fun hj => gaugeExt_bedge_gt hp hq hW0 hcoh htree hj)
    (hblt := fun hj => gaugeExt_bedge_lt hp hq hW0 hcoh htree hj)
    (hcu := hcu) (hwin := hwin)
  -- transport from the global gauge back to `Wt`
  obtain ⟨φ, ψ, hleft, hρ, hr⟩ := betaCast_spec (Wt := Wt) (Wt' := gaugeExt p q hq Wt)
    (c := tlW p q) (lo := 0) (hi := (p : ℤ) * (q : ℤ))
    (fun e he => coverClassAt_gaugeExt_of_band he)
  have hψr : FreeGroup.map ψ
      (winRoot (gaugeExt p q hq Wt) (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q)) =
      winRoot Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q) := by
    rw [← hr]
    exact hleft _
  have hψR : FreeGroup.map ψ
      ((winRoot (gaugeExt p q hq Wt) (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q)) ^ l) =
      (winRoot Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q)) ^ l := by
    rw [map_pow, hψr]
  have hmap : (Subgroup.normalClosure
        ({(winRoot (gaugeExt p q hq Wt) (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q)) ^ l} :
          Set (FreeGroup (winBeta (gaugeExt p q hq Wt) (tlW p q) 0 ((p : ℤ) * (q : ℤ)))))).map
        (FreeGroup.map ψ) ≤
      Subgroup.normalClosure
        ({(winRoot Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q)) ^ l} :
          Set (FreeGroup (winBeta Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ))))) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine Subgroup.normalClosure_le_normal fun y hy => ?_
    refine Subgroup.mem_comap.mpr ?_
    rw [Set.mem_singleton_iff] at hy
    rw [hy, hψR]
    exact Subgroup.subset_normalClosure (Set.mem_singleton _)
  intro x hx
  have hmem : winRho (gaugeExt p q hq Wt) (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (FreeGroup.map φ x) ∈
      Subgroup.normalClosure ({tlU p q ^ l} : Set (FreeGroup (Fin 2))) := by
    rw [hρ]
    exact hx
  have hmapx : FreeGroup.map ψ (FreeGroup.map φ x) ∈
      Subgroup.normalClosure ({(winRoot Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q)) ^ l} :
        Set (FreeGroup (winBeta Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ))))) :=
    hmap (Subgroup.mem_map_of_mem (FreeGroup.map ψ) (hglob (FreeGroup.map φ x) hmem))
  rwa [hleft x] at hmapx


/-! ## The class map as the gauge map -/

/-- **`winRho` is the gauge map precomposed with the inclusion of the non-tree edges.**  On a
generator `e : winBeta` both sides are `coverClassAt Wt c e.1`, so this is the identity of the
composites; it is what lets the level-complex statements (about `gaugeMap` on `F (Fin 2 × ℤ)`) be
applied to the vertex statement (about `winRho` on `F (winBeta)`). -/
theorem winRho_eq_gaugeMap {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    winRho Wt c lo hi =
      (gaugeMap Wt c).comp
        (FreeGroup.map (Subtype.val : winBeta Wt c lo hi → α × ℤ)) := by
  refine FreeGroup.ext_hom _ _ fun e => ?_
  simp only [MonoidHom.comp_apply, FreeGroup.map.of, winRho_of, gaugeMap_of]
  rfl

theorem twoLetterFreiheitssatz (p q l : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hl : 1 ≤ l)
    (hcop : Nat.Coprime p q)
    {c : Fin 2 → ℤ} {τ : FreeGroup (Fin 2)} {lo hi : ℤ} {Wt : ℤ → FreeGroup (Fin 2)}
    (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i)
    (hcu : Work.OROneRel.cohom c (Work.OROneRel.tlU p q) = 1)
    (hτ : Work.OROneRel.cohom c τ = Multiplicative.ofAdd 1)
    (hwin : ∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE c lo hi)
    (hone : ∀ k : ℤ, k ≠ 0 →
      ¬ (∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
          lo ≤ e.1.2 + k ∧ lo ≤ e.1.2 + c e.1.1 + k ∧ e.1.2 + k ≤ hi ∧ e.1.2 + c e.1.1 + k ≤ hi))
    (htree : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈ Work.OROneRel.winTree Wt c lo hi) :
    ∀ x : FreeGroup (Work.OROneRel.winBeta Wt c lo hi),
      Work.OROneRel.winRho Wt c lo hi x ∈
          Subgroup.normalClosure ({Work.OROneRel.tlU p q ^ l} : Set (FreeGroup (Fin 2))) →
        x ∈ Subgroup.normalClosure
          ({Work.OROneRel.winRoot Wt c lo hi (Work.OROneRel.tlU p q) ^ l} :
            Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))) := by
  rcases c_eq_tlW_or p q hcop hcu hτ with ⟨hc0, hc1⟩ | ⟨hc0, hc1⟩
  · -- the weight is `tlW p q`
    have hc : c = tlW p q := by
      funext i
      fin_cases i
      · simpa [tlW] using hc0
      · simpa [tlW] using hc1
    rw [hc] at hcoh hcu hτ hwin hone htree ⊢
    obtain ⟨hlo, hhi⟩ := window_eq_band_tlW p q hp hq hwin hone
    rw [hlo, hhi] at hwin hone htree ⊢
    exact twoLetterFreiheitssatz_band p q l hp hq hl hcop hW0 hcoh hcu hτ hwin hone htree
  · -- the weight is `-tlW p q`: reflect to the previous case
    have hc : c = fun a => -tlW p q a := by
      funext i
      fin_cases i
      · simpa [tlW] using hc0
      · simpa [tlW] using hc1
    rw [hc] at hcoh hcu hτ hwin hone htree ⊢
    refine twoLetterFreiheitssatz_neg_of_pos p q l hp hq hl ?_ hW0 hcoh hcu ⟨τ, hτ⟩ hwin hone htree
    intro Wt' lo' hi' hW0' hcoh' hcu' hτ' hwin' hone' htree'
    obtain ⟨hlo', hhi'⟩ := window_eq_band_tlW p q hp hq hwin' hone'
    rw [hlo', hhi'] at hwin' hone' htree' ⊢
    exact twoLetterFreiheitssatz_band p q l hp hq hl hcop (τ := hτ'.choose) hW0' hcoh' hcu'
      hτ'.choose_spec hwin' hone' htree'

end Work.OROneRel
