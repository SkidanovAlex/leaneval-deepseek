/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# `Work.OROneRel.winGate_inj_of_spanning_bad` is FALSE -- machine-checked refutation

The delegated statement says: for a relator `u` of a one-relator group `⟨α | u ^ l⟩`, a weight
`c : α → ℤ` killing `u`, a gauge `Wt` of the `ℤ`-cover, a window `[lo,hi]` satisfying the band
conditions (`hwin`, `hone`, `htree`), the `ℤ`-domain axioms (`hZ`) and the spanning condition for the
levels of the gate (`hspan`), and provided every letter of `u` has non-zero exponent sum (`hbad`),
the free group on the *gate* alphabet `winBetaSub Wt c S` (with
`S = {e ∈ winE c lo hi | (e.1, e.2 - 1) ∈ winE c lo hi}`) maps **injectively** into
`⟨α | u ^ l⟩` by the loop-class map.

The counterexample below shows that this is false: `hbad` does not prevent a *gate* edge from being
the single non-tree edge traversed by the walk, in which case the gate's class is (a power of) `u`
itself.

## The data

* `α = Fin 2`, `a := of 0`, `b := of 1`, weights `c a = c b = -1`
  (so every edge moves one level *down*; a word of level `i` is `b ^ (-i)` up to weight-zero
  factors);
* `u = b⁻¹ * a⁻¹ * b * b = b⁻¹ a⁻¹ b²`, so `eps a u = -1`, `eps b u = 1` (all non-zero, `hbad`),
  `relatorNorm u = 4`, `u` is not a proper power, and `cohom c u = 1`;
* the gauge `Wt 0 = 1`, `Wt 1 = b⁻¹`, `Wt 2 = b⁻¹ a⁻¹` (the tree-path gauge of the band `[0,2]`),
  extended by powers of `b⁻¹` outside `[0,2]` so that `cohom c (Wt i) = ofAdd i` for every `i`;
* the window `lo = 0`, `hi = 2` (the band of the walk of `u`), and `l = 1`.

## Why the conclusion fails

The walk of `u` is `[((b,1),·), ((a,2),·), ((b,2),·), ((b,1),·)]`; among its traversals exactly one
has non-trivial loop class, namely the traversal of the edge `(b,2)`, and that edge lies in the gate
`S = {(a,2), (b,2)}`, since `(b,1) ∈ winE c 0 2`.  Its loop class is

`coverClassAt Wt c (b,2) = Wt 2 * b * (Wt 1)⁻¹ = b⁻¹a⁻¹ * b * b = u`,

so the generator `of ⟨(b,2)⟩` of `F (winBetaSub Wt c S)` -- a non-trivial element -- is mapped to
`mk u = 1` in `⟨a, b | u ^ 1⟩`.  Hence the map is not injective.

The mechanism: `hbad` forbids only the `wfbBandCounter` datum (where the relator's letters had
vanishing exponent sum); it does not forbid a gate edge from having class `u`.  Note that in this
example the gate edge `(b,2)` *does* move levels (`c b = -1 ≠ 0`), so the intuition recorded in
`magnusStepCase2.lean` ("with all exponent sums non-zero every gate edge moves levels", used to
justify the `hbad` repair) is not sufficient.
-/
import Mathlib
import Submission.Work.OROneRel.winGateDefs
import Submission.Work.OROneRel.zDomainWindowDefs
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel.WGCounter

open Work.OROneRel

/-! ## The data -/

/-- The generator `a = of 0`. -/
abbrev A : FreeGroup (Fin 2) := FreeGroup.of 0

/-- The generator `b = of 1`. -/
abbrev B : FreeGroup (Fin 2) := FreeGroup.of 1

/-- The weight: both generators move one level down. -/
abbrev c : Fin 2 → ℤ := fun _ => -1

/-- The relator `u = b⁻¹ a⁻¹ b²`. -/
abbrev u : FreeGroup (Fin 2) := B⁻¹ * A⁻¹ * B * B

/-- The gauge: the tree-path gauge of the band `[0,2]` (`1`, `b⁻¹`, `b⁻¹a⁻¹`), extended by powers of
`b⁻¹` outside the window (so that its weight is the level everywhere). -/
noncomputable def Wt : ℤ → FreeGroup (Fin 2) := fun i =>
  if i = 0 then 1 else if i = 1 then B⁻¹ else if i = 2 then B⁻¹ * A⁻¹
    else if i < 0 then (B⁻¹) ^ i else B⁻¹ * A⁻¹ * (B⁻¹) ^ (i - 2)

/-- The lower end of the window. -/
abbrev lo : ℤ := 0

/-- The upper end of the window. -/
abbrev hi : ℤ := 2

/-- The gate alphabet of the statement: the edges of the window whose down-translate is again an
edge of the window. -/
abbrev S : Set (Fin 2 × ℤ) := {e : Fin 2 × ℤ | e ∈ winE c lo hi ∧ (e.1, e.2 - 1) ∈ winE c lo hi}

theorem S_sub : S ⊆ winE c lo hi := fun _ he => he.1

/-! ## Elementary evaluations -/

theorem Wt_zero : Wt 0 = 1 := by simp [Wt]

theorem Wt_one : Wt 1 = B⁻¹ := by simp [Wt]

theorem Wt_two : Wt 2 = B⁻¹ * A⁻¹ := by simp [Wt]

theorem wordOf_eq_toWord (w : FreeGroup (Fin 2)) :
    wordOf w = @FreeGroup.toWord (Fin 2) (inferInstance) w := by
  rw [Work.OROneRel.wordOf]
  exact congrArg (fun (inst : DecidableEq (Fin 2)) => @FreeGroup.toWord (Fin 2) inst w)
    (Subsingleton.elim _ _)

theorem toWord_A : @FreeGroup.toWord (Fin 2) (inferInstance) A = [((0 : Fin 2), true)] := by
  rw [A, FreeGroup.toWord_of]

theorem toWord_B : @FreeGroup.toWord (Fin 2) (inferInstance) B = [((1 : Fin 2), true)] := by
  rw [B, FreeGroup.toWord_of]

theorem wordOf_A : wordOf A = [((0 : Fin 2), true)] := (wordOf_eq_toWord A).trans toWord_A

theorem wordOf_B : wordOf B = [((1 : Fin 2), true)] := (wordOf_eq_toWord B).trans toWord_B

theorem wordOf_one : wordOf (1 : FreeGroup (Fin 2)) = [] := by
  rw [wordOf_eq_toWord, FreeGroup.toWord_one]

theorem wordOf_Binv : wordOf (B⁻¹) = [((1 : Fin 2), false)] := by
  rw [wordOf_eq_toWord, FreeGroup.toWord_inv, toWord_B]
  rfl

theorem wordOf_Binv_Ainv : wordOf (B⁻¹ * A⁻¹) = [((1 : Fin 2), false), ((0 : Fin 2), false)] := by
  rw [wordOf_eq_toWord, FreeGroup.toWord_mul, FreeGroup.toWord_inv, FreeGroup.toWord_inv, toWord_B,
    toWord_A]
  decide

theorem toWord_u :
    @FreeGroup.toWord (Fin 2) (inferInstance) u =
      [((1 : Fin 2), false), ((0 : Fin 2), false), ((1 : Fin 2), true), ((1 : Fin 2), true)] := by
  simp only [u, FreeGroup.toWord_mul, FreeGroup.toWord_inv, FreeGroup.toWord_of]
  decide

theorem wordOf_u :
    wordOf u =
      [((1 : Fin 2), false), ((0 : Fin 2), false), ((1 : Fin 2), true), ((1 : Fin 2), true)] :=
  (wordOf_eq_toWord u).trans toWord_u

theorem decor_u :
    decor c 0 (wordOf u) =
      [(((1 : Fin 2), (1 : ℤ)), false), (((0 : Fin 2), (2 : ℤ)), false),
       (((1 : Fin 2), (2 : ℤ)), true), (((1 : Fin 2), (1 : ℤ)), true)] := by
  rw [wordOf_u]
  rfl

theorem decor_Wt_zero : decor c 0 (wordOf (Wt 0)) = [] := by
  rw [Wt_zero, wordOf_one]
  rfl

theorem decor_Wt_one : decor c 0 (wordOf (Wt 1)) = [(((1 : Fin 2), (1 : ℤ)), false)] := by
  rw [Wt_one, wordOf_Binv]
  rfl

theorem decor_Wt_two :
    decor c 0 (wordOf (Wt 2)) =
      [(((1 : Fin 2), (1 : ℤ)), false), (((0 : Fin 2), (2 : ℤ)), false)] := by
  rw [Wt_two, wordOf_Binv_Ainv]
  rfl

/-! ## The loop classes of the four window edges -/

theorem class_B2 : coverClassAt Wt c ((1 : Fin 2), (2 : ℤ)) = u := by
  rw [coverClassAt, gaugeMap_of, show (2 : ℤ) + c 1 = 1 from by simp [c]]
  rw [Wt_two, Wt_one]
  simp only [u]
  group

theorem class_B1 : coverClassAt Wt c ((1 : Fin 2), (1 : ℤ)) = 1 := by
  rw [coverClassAt, gaugeMap_of, show (1 : ℤ) + c 1 = 0 from by simp [c]]
  rw [Wt_one, Wt_zero]
  group

theorem class_A2 : coverClassAt Wt c ((0 : Fin 2), (2 : ℤ)) = 1 := by
  rw [coverClassAt, gaugeMap_of, show (2 : ℤ) + c 0 = 1 from by simp [c]]
  rw [Wt_two, Wt_one]
  group

theorem class_A1 : coverClassAt Wt c ((0 : Fin 2), (1 : ℤ)) = B⁻¹ * A := by
  rw [coverClassAt, gaugeMap_of, show (1 : ℤ) + c 0 = 0 from by simp [c]]
  rw [Wt_one, Wt_zero]
  group

theorem toWord_Binv_A : @FreeGroup.toWord (Fin 2) (inferInstance) (B⁻¹ * A) =
    [((1 : Fin 2), false), ((0 : Fin 2), true)] := by
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_inv, toWord_B, toWord_A]
  decide

theorem u_ne_one : u ≠ 1 := by
  intro h
  have h2 : @FreeGroup.toWord (Fin 2) (inferInstance) u = [] := by rw [h, FreeGroup.toWord_one]
  rw [toWord_u] at h2
  exact absurd h2 (by decide)

theorem class_A1_ne_one : coverClassAt Wt c ((0 : Fin 2), (1 : ℤ)) ≠ 1 := by
  rw [class_A1]
  intro h
  have h2 : @FreeGroup.toWord (Fin 2) (inferInstance) (B⁻¹ * A) = [] := by
    rw [h, FreeGroup.toWord_one]
  rw [toWord_Binv_A] at h2
  exact absurd h2 (by decide)

/-! ## The exponent sums, the norm, and aperiodicity of `u` -/

theorem eps_zero_u : eps (0 : Fin 2) u = -1 := by
  rw [show eps (0 : Fin 2) u = wordEps 0 (wordOf u) from rfl, wordOf_u]
  simp only [wordEps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num

theorem eps_one_u : eps (1 : Fin 2) u = 1 := by
  rw [show eps (1 : Fin 2) u = wordEps 1 (wordOf u) from rfl, wordOf_u]
  simp only [wordEps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num

theorem relatorNorm_u : relatorNorm u = 4 := by
  rw [show relatorNorm u = (wordOf u).length from rfl, wordOf_u]
  rfl

theorem cohom_A : cohom c A = Multiplicative.ofAdd (-1 : ℤ) := by
  rw [A, cohom_of]

theorem cohom_B : cohom c B = Multiplicative.ofAdd (-1 : ℤ) := by
  rw [B, cohom_of]

theorem cohom_Binv : cohom c B⁻¹ = Multiplicative.ofAdd (1 : ℤ) := by
  rw [map_inv, cohom_B, ← ofAdd_neg]
  norm_num

theorem cohom_u : cohom c u = 1 := by
  rw [u, map_mul, map_mul, map_mul, map_inv, map_inv, cohom_B, cohom_A]
  decide

/-- `u` is not a proper power: the projection onto the generator `a` maps `u` to `ofAdd (-1)`, so
`u = v ^ k` would force `k * z = -1`. -/
theorem not_isProperPower_u : ¬ IsProperPower u := by
  rintro ⟨v, k, hk, huk⟩
  let f : Fin 2 → Multiplicative ℤ := fun x => if x = 0 then Multiplicative.ofAdd (1 : ℤ) else 1
  have h1 : FreeGroup.lift f u = (FreeGroup.lift f v) ^ k := by rw [huk, map_pow]
  have hval : FreeGroup.lift f u = Multiplicative.ofAdd (-1 : ℤ) := by
    rw [u, map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [show FreeGroup.lift f B = 1 from by
          rw [B, FreeGroup.lift_apply_of]; simp [f],
        show FreeGroup.lift f A = Multiplicative.ofAdd (1 : ℤ) from by
          rw [A, FreeGroup.lift_apply_of]; simp [f]]
    simp
  rw [hval] at h1
  have h2 : (-1 : ℤ) = (k : ℤ) * (FreeGroup.lift f v).toAdd := by
    have := congrArg Multiplicative.toAdd h1
    simpa [Int.toAdd_pow] using this
  have h3 : (k : ℤ) * (-(FreeGroup.lift f v).toAdd) = 1 := by linarith
  have h4 : (k : ℤ) = 1 ∨ (k : ℤ) = -1 := Int.eq_one_or_neg_one_of_mul_eq_one h3
  have hk2 : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  omega

/-! ## The window `[0,2]` and its edges -/

theorem mem_winE_iff (e : Fin 2 × ℤ) :
    e ∈ winE c lo hi ↔ (0 ≤ e.2 ∧ e.2 ≤ 2 ∧ 0 ≤ e.2 + c e.1 ∧ e.2 + c e.1 ≤ 2) := by
  simp [winE, lo, hi]

theorem wE_01 : (((0 : Fin 2), (1 : ℤ)) : Fin 2 × ℤ) ∈ winE c lo hi := by
  rw [mem_winE_iff]; simp [c]

theorem wE_02 : (((0 : Fin 2), (2 : ℤ)) : Fin 2 × ℤ) ∈ winE c lo hi := by
  rw [mem_winE_iff]; simp [c]

theorem wE_11 : (((1 : Fin 2), (1 : ℤ)) : Fin 2 × ℤ) ∈ winE c lo hi := by
  rw [mem_winE_iff]; simp [c]

theorem wE_12 : (((1 : Fin 2), (2 : ℤ)) : Fin 2 × ℤ) ∈ winE c lo hi := by
  rw [mem_winE_iff]; simp [c]

theorem not_wE_00 : (((0 : Fin 2), (0 : ℤ)) : Fin 2 × ℤ) ∉ winE c lo hi := by
  rw [mem_winE_iff]; simp [c]

theorem not_wE_10 : (((1 : Fin 2), (0 : ℤ)) : Fin 2 × ℤ) ∉ winE c lo hi := by
  rw [mem_winE_iff]; simp [c]

/-! ## The gate `S` and its levels -/

theorem mem_S_02 : (((0 : Fin 2), (2 : ℤ)) : Fin 2 × ℤ) ∈ S := ⟨wE_02, by simpa using wE_01⟩

theorem mem_S_12 : (((1 : Fin 2), (2 : ℤ)) : Fin 2 × ℤ) ∈ S := ⟨wE_12, by simpa using wE_11⟩

/-- **The structural fact behind the counterexample.**  Every edge of the gate has level `2`: its
down-translate `(x, i - 1)` lies in the window, and `c x = -1`, so `i - 1 - 1 ≥ 0`. -/
theorem snd_eq_two_of_mem_S {x : Fin 2} {i : ℤ} (he : ((x, i) : Fin 2 × ℤ) ∈ S) : i = 2 := by
  have h1 : 0 ≤ i - 1 + c x := ((mem_winE_iff ((x, i - 1))).mp he.2).2.2.1
  have h2 : i ≤ 2 := ((mem_winE_iff ((x, i))).mp he.1).2.1
  have hc : c x = -1 := rfl
  omega

theorem lvLevels_S {l : ℤ} (hl : l ∈ lvLevels c S) : l = 1 ∨ l = 2 := by
  obtain ⟨e, he, hdisj⟩ := hl
  obtain ⟨x, i⟩ := e
  have hi2 : i = 2 := snd_eq_two_of_mem_S he
  rcases hdisj with hsrc | htgt
  · rw [lvSrc_def, hi2] at hsrc
    exact Or.inr hsrc.symm
  · rw [lvTgt_def, hi2] at htgt
    have hc : c x = -1 := rfl
    rw [hc] at htgt
    exact Or.inl (by omega)

theorem lvJoined_S_12 : lvJoined c S 1 2 :=
  Relation.ReflTransGen.single
    ⟨((1 : Fin 2), (2 : ℤ)), mem_S_12,
      Or.inr ⟨by simp [lvSrc_def], by simp [lvTgt_def, c]⟩⟩

theorem lvJoined_S_21 : lvJoined c S 2 1 :=
  Relation.ReflTransGen.single
    ⟨((1 : Fin 2), (2 : ℤ)), mem_S_12,
      Or.inl ⟨by simp [lvSrc_def], by simp [lvTgt_def, c]⟩⟩

/-! ## The tree of the window -/

theorem mem_winTree_11 : (((1 : Fin 2), (1 : ℤ)) : Fin 2 × ℤ) ∈ winTree Wt c lo hi :=
  ⟨wE_11, class_B1⟩

theorem mem_winTree_02 : (((0 : Fin 2), (2 : ℤ)) : Fin 2 × ℤ) ∈ winTree Wt c lo hi :=
  ⟨wE_02, class_A2⟩

theorem mem_TS_02 :
    (((0 : Fin 2), (2 : ℤ)) : Fin 2 × ℤ) ∈ winTree Wt c lo hi ∩ S :=
  ⟨mem_winTree_02, mem_S_02⟩

theorem lvJoined_TS_12 : lvJoined c (winTree Wt c lo hi ∩ S) 1 2 :=
  Relation.ReflTransGen.single
    ⟨((0 : Fin 2), (2 : ℤ)), mem_TS_02,
      Or.inr ⟨by simp [lvSrc_def], by simp [lvTgt_def, c]⟩⟩

theorem lvJoined_TS_21 : lvJoined c (winTree Wt c lo hi ∩ S) 2 1 :=
  Relation.ReflTransGen.single
    ⟨((0 : Fin 2), (2 : ℤ)), mem_TS_02,
      Or.inl ⟨by simp [lvSrc_def], by simp [lvTgt_def, c]⟩⟩

/-! ## The hypotheses of the statement -/

theorem hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi := by
  intro p hp
  rw [decor_u] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h
  · rw [h]; exact wE_11
  · rw [h]; exact wE_02
  · rw [h]; exact wE_12
  · rw [h]; exact wE_11

theorem hone : ∀ k : ℤ, k ≠ 0 →
    ¬ (∀ p ∈ decor c 0 (wordOf u),
        lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧ p.1.2 + k ≤ hi ∧
          p.1.2 + c p.1.1 + k ≤ hi) := by
  intro k hk h
  have hp1 : (((1 : Fin 2), (1 : ℤ)), false) ∈ decor c 0 (wordOf u) := by
    rw [decor_u]; decide
  have hp2 : (((1 : Fin 2), (2 : ℤ)), true) ∈ decor c 0 (wordOf u) := by
    rw [decor_u]; decide
  have h1 := h _ hp1
  have h2 := h _ hp2
  simp only [lo, hi, c] at h1 h2
  omega

theorem htree : ∀ i : ℤ, lo ≤ i → i ≤ hi →
    ∀ q ∈ decor c 0 (wordOf (Wt i)), coverEdge q ∈ winTree Wt c lo hi := by
  intro i hli hhi q hq
  interval_cases i
  · rw [decor_Wt_zero] at hq
    simp at hq
  · rw [decor_Wt_one] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    exact mem_winTree_11
  · rw [decor_Wt_two] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hq' | hq'
    · subst hq'; exact mem_winTree_11
    · subst hq'; exact mem_winTree_02

theorem hZ_covers : ∀ x : Fin 2, ∃ i : ℤ, (x, i) ∈ winE c lo hi := by
  intro x
  fin_cases x
  · exact ⟨1, wE_01⟩
  · exact ⟨1, wE_11⟩

theorem hZ_nested : ∀ e ∈ winE c lo hi, ∀ i : ℤ, 1 ≤ i → lvShift (-i) e ∈ winE c lo hi →
    ∀ j : ℤ, 1 ≤ j → j ≤ i → lvShift (-j) e ∈ winE c lo hi := by
  intro e he i h1i hsh j h1j hji
  obtain ⟨x, m⟩ := e
  rw [mem_winE_iff] at he hsh ⊢
  simp only [lvShift_fst, lvShift_snd] at he hsh ⊢
  obtain ⟨h1, h2, h3, h4⟩ := he
  obtain ⟨g1, g2, g3, g4⟩ := hsh
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem hZ_inter_nonempty : ∃ e : Fin 2 × ℤ, e ∈ winE c lo hi ∧ lvShift (-1) e ∈ winE c lo hi :=
  ⟨((1 : Fin 2), (2 : ℤ)), wE_12, by simpa [lvShift] using wE_11⟩

theorem hZ_inter_connected : ∀ l m : ℤ, l ∈ lvLevels c S → m ∈ lvLevels c S → lvJoined c S l m := by
  intro l m hl hm
  have hl' := lvLevels_S hl
  have hm' := lvLevels_S hm
  rcases hl' with rfl | rfl <;> rcases hm' with rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact lvJoined_S_12
  · exact lvJoined_S_21
  · exact Relation.ReflTransGen.refl

theorem hZ : IsZDomain c (winE c lo hi) :=
  ⟨hZ_covers, hZ_nested, hZ_inter_nonempty, hZ_inter_connected⟩

theorem hspan : ∀ l m : ℤ, l ∈ lvLevels c S → m ∈ lvLevels c S →
    lvJoined c (winTree Wt c lo hi ∩ S) l m := by
  intro l m hl hm
  have hl' := lvLevels_S hl
  have hm' := lvLevels_S hm
  rcases hl' with rfl | rfl <;> rcases hm' with rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact lvJoined_TS_12
  · exact lvJoined_TS_21
  · exact Relation.ReflTransGen.refl

theorem cohom_A_inv : cohom c A⁻¹ = Multiplicative.ofAdd (1 : ℤ) := by
  rw [map_inv, cohom_A, ← ofAdd_neg]
  norm_num

theorem cohom_Binv_zpow (n : ℤ) : cohom c ((B⁻¹) ^ n) = Multiplicative.ofAdd n := by
  rw [map_zpow, cohom_Binv, ← ofAdd_zsmul]
  simp

theorem hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i := by
  intro i
  by_cases h0 : i = 0
  · subst h0; rw [Wt_zero, map_one]; rfl
  by_cases h1 : i = 1
  · subst h1; rw [Wt_one, cohom_Binv]
  by_cases h2 : i = 2
  · subst h2
    rw [Wt_two, map_mul, cohom_Binv, cohom_A_inv, ← ofAdd_add]
    norm_num
  · by_cases hneg : i < 0
    · rw [Wt, if_neg h0, if_neg h1, if_neg h2, if_pos hneg, cohom_Binv_zpow]
    · rw [Wt, if_neg h0, if_neg h1, if_neg h2, if_neg hneg, map_mul, map_mul, cohom_Binv,
        cohom_A_inv, cohom_Binv_zpow, ← ofAdd_add, ← ofAdd_add]
      congr 1
      ring

/-! ## The conclusion fails: `of ⟨(b,2)⟩` is in the kernel -/

/-- The gate generator whose class is `u`. -/
noncomputable abbrev e2 : winBetaSub Wt c S :=
  ⟨((1 : Fin 2), (2 : ℤ)), mem_S_12, by rw [class_B2]; exact u_ne_one⟩

theorem winRho_e2 : winRho Wt c lo hi (winBetaSubIncl Wt c S_sub (FreeGroup.of e2)) = u := by
  rw [winBetaSubIncl_of, winRho_of]
  show coverClassAt Wt c ((winBetaSubVal Wt c S_sub e2).1) = u
  rw [winBetaSubVal_coe]
  exact class_B2

theorem of_e2_ne_one : (FreeGroup.of e2 : FreeGroup (winBetaSub Wt c S)) ≠ 1 := by
  classical
  intro h
  have h2 : (FreeGroup.of e2).toWord = ([] : List (winBetaSub Wt c S × Bool)) := by
    rw [h, FreeGroup.toWord_one]
  rw [FreeGroup.toWord_of] at h2
  exact absurd h2 (by simp)

theorem mk_u_eq_one : PresentedGroup.mk ({u ^ 1} : Set (FreeGroup (Fin 2))) u = 1 := by
  rw [PresentedGroup.mk]
  refine (QuotientGroup.eq_one_iff u).mpr ?_
  have h : (u : FreeGroup (Fin 2)) ∈ ({u ^ 1} : Set (FreeGroup (Fin 2))) := by
    simp only [pow_one, Set.mem_singleton_iff]
  exact Subgroup.subset_normalClosure h

theorem not_injective :
    ¬ Function.Injective
      (fun x : FreeGroup (winBetaSub Wt c S) =>
        PresentedGroup.mk ({u ^ 1} : Set (FreeGroup (Fin 2)))
          (winRho Wt c lo hi (winBetaSubIncl Wt c S_sub x))) := by
  intro hinj
  have h1 : PresentedGroup.mk ({u ^ 1} : Set (FreeGroup (Fin 2)))
        (winRho Wt c lo hi (winBetaSubIncl Wt c S_sub (FreeGroup.of e2))) =
      PresentedGroup.mk ({u ^ 1} : Set (FreeGroup (Fin 2)))
        (winRho Wt c lo hi (winBetaSubIncl Wt c S_sub 1)) := by
    rw [winRho_e2, mk_u_eq_one]
    simp
  have h2 : (FreeGroup.of e2 : FreeGroup (winBetaSub Wt c S)) = 1 := hinj h1
  exact of_e2_ne_one h2

/-! ## The statement, and its refutation -/

/-- The delegated statement, as a `Prop` (at universe `0`, which is the instance refuted below). -/
abbrev WGHyp : Prop :=
  ∀ (α : Type) (u : FreeGroup α) (l : ℕ), 1 ≤ l → ¬ IsProperPower u → 2 ≤ relatorNorm u →
    (∀ x : α, x ∈ relatorLetters u → eps x u ≠ 0) →
    ∀ (c : α → ℤ) (τ : FreeGroup α) (Wt : ℤ → FreeGroup α) (lo hi : ℤ),
      Wt 0 = 1 →
      (∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i) →
      cohom c u = 1 →
      cohom c τ = Multiplicative.ofAdd 1 →
      (∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi) →
      (∀ k : ℤ, k ≠ 0 →
        ¬ (∀ p ∈ decor c 0 (wordOf u),
            lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧ p.1.2 + k ≤ hi ∧
              p.1.2 + c p.1.1 + k ≤ hi)) →
      (∀ i : ℤ, lo ≤ i → i ≤ hi →
        ∀ q ∈ decor c 0 (wordOf (Wt i)), coverEdge q ∈ winTree Wt c lo hi) →
      IsZDomain c (winE c lo hi) →
      (∀ l m : ℤ,
        l ∈ lvLevels c
            {e : α × ℤ | e ∈ winE c lo hi ∧ (e.1, e.2 - 1) ∈ winE c lo hi} →
        m ∈ lvLevels c
            {e : α × ℤ | e ∈ winE c lo hi ∧ (e.1, e.2 - 1) ∈ winE c lo hi} →
        lvJoined c
          (winTree Wt c lo hi ∩
            {e : α × ℤ | e ∈ winE c lo hi ∧ (e.1, e.2 - 1) ∈ winE c lo hi}) l m) →
      Function.Injective
        (fun x : FreeGroup (winBetaSub Wt c
            {e : α × ℤ | e ∈ winE c lo hi ∧ (e.1, e.2 - 1) ∈ winE c lo hi}) =>
          PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
            (winRho Wt c lo hi
              (winBetaSubIncl Wt c (lo := lo) (hi := hi) (fun e he => he.1) x)))

/-- **The delegated statement is FALSE**: the data above satisfies all of its hypotheses, but the
generator `of ⟨(b,2)⟩` of the gate free group is a non-trivial element of the kernel of the class map
into `⟨a, b | u ^ 1⟩`. -/
theorem wg_refute (H : WGHyp) : False := by
  refine not_injective (H (Fin 2) u 1 le_rfl not_isProperPower_u ?_ ?_ c B⁻¹ Wt lo hi Wt_zero
    hcoh cohom_u ?_ hwin hone htree hZ ?_)
  · rw [relatorNorm_u]; norm_num
  · intro x _
    fin_cases x
    · show eps (0 : Fin 2) u ≠ 0
      rw [eps_zero_u]; norm_num
    · show eps (1 : Fin 2) u ≠ 0
      rw [eps_one_u]; norm_num
  · rw [cohom_Binv]
  · exact hspan

end Work.OROneRel.WGCounter
