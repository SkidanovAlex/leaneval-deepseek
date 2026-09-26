import Mathlib.Analysis.Normed.Order.Lattice

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.Topology.Exhaustion

/-- **The ordered-initial-segment exhaustion assembly (canonical length form)**:
`X` is exhausted by the nested open images of the maps `i n`, each `i n` an
injective continuous open embedding of the real interval `(0, L n)` with
`0 < L n ≤ L (n+1) ≤ 1`; the embeddings AGREE on the common coordinate value
(`i n t = i (n+1) ⟨t.1, …⟩`, i.e. `range (i n)` sits in `range (i (n+1))` as the
initial segment `(0, L n)` of its coordinate), and the images cover `X`.  Then
`X` carries the well-defined coordinate `c(x) = t.1` for any `n` with
`x = i n t`, a homeomorphism of `X` onto the interval `(0, sSup (range L))`.
Proof outline: with `S := sSup (range L)` (positive by `hLpos`+`hLle1`), the
preimage interval `(0, L n)` embeds into `(0, S)` by inclusion and the
agreement hypothesis makes the inclusions compatible, so the maps `i n`
paste to a single map `e : {t : ℝ // t ∈ Ioo 0 S} → X` (`e t = i n t` for any
`n` with `t.1 < L n`, well-defined by the agreement chain `i n t = i m t` for
`n ≤ m`); `e` is injective (two points have parameters `< L n, L m`, pick a
common larger `k` and use agreement + `hiInj k`), surjective (`hiCover`),
continuous (on the open set `{t | t.1 < L n}` of the domain it equals
`i n` composed with the inclusion — paste by
`continuous_of_cover_nhds` over the cover `{t | t.1 < L n}` which covers the
domain because `t.1 < S` gives `∃ n, t.1 < L n` by
`exists_lt_of_lt_csSup`/`lt_csSup_iff`), and an open map (on the same local
pieces `e = i n ∘ inclusion`, the inclusion is a homeo onto
`{t | t.1 < L n}` and `hiOpenMap` makes `i n` open), hence a homeomorphism
(`Homeomorph.ofBijective` or `Equiv.ofBijective` + `toHomeomorphOfContinuousOpen`). -/
theorem chain_initialSegments_union_homeo {X : Type*} [TopologicalSpace X] [Nonempty X]
    (L : ℕ → ℝ) (hLpos : ∀ n, 0 < L n) (hLmono : ∀ n, L n ≤ L (n + 1))
    (hLle1 : ∀ n, L n ≤ 1)
    (i : ∀ n, {t : ℝ // t ∈ Set.Ioo 0 (L n)} → X)
    (hiCont : ∀ n, Continuous (i n))
    (hiInj : ∀ n, Function.Injective (i n))
    (hiOpenMap : ∀ n, ∀ U : Set {t : ℝ // t ∈ Set.Ioo 0 (L n)}, IsOpen U →
      IsOpen (i n '' U))
    (hiAgree : ∀ n, ∀ t : {t : ℝ // t ∈ Set.Ioo 0 (L n)},
      i n t = i (n + 1) ⟨t.1, ⟨t.2.1, lt_of_lt_of_le t.2.2 (hLmono n)⟩⟩)
    (hiCover : ∀ x : X, ∃ n, ∃ t : {t : ℝ // t ∈ Set.Ioo 0 (L n)}, i n t = x) :
    Nonempty ({t : ℝ // t ∈ Set.Ioo 0 (sSup (Set.range L))} ≃ₜ X) := by
  let S : ℝ := sSup (Set.range L)
  let A := {t : ℝ // t ∈ Set.Ioo 0 S}
  -- facts about the supremum S
  have hbdd : BddAbove (Set.range L) := ⟨1, by
    intro y hy
    rcases hy with ⟨n, hn⟩
    simpa [hn] using hLle1 n⟩
  have hLleS : ∀ n : ℕ, L n ≤ S := fun n => le_csSup hbdd ⟨n, rfl⟩
  have hne : (Set.range L).Nonempty := ⟨L 0, ⟨0, rfl⟩⟩
  have hexists : ∀ a : ℝ, a < S → ∃ n : ℕ, a < L n := by
    intro a ha
    rcases exists_lt_of_lt_csSup hne ha with ⟨b, hb, hab⟩
    rcases hb with ⟨n, rfl⟩
    exact ⟨n, hab⟩
  -- monotonicity of L along chains of indices
  have hmono_chain : ∀ {n m : ℕ}, n ≤ m → L n ≤ L m := by
    intro n m hnm
    exact Nat.le_induction (m := n) (P := fun k _ => L n ≤ L k)
      (le_rfl) (fun k _ ih => le_trans ih (hLmono k)) m hnm
  -- the agreement chain: i n t = i m t for every m ≥ n (coordinate preserved)
  have hchain : ∀ {n m : ℕ} (hnm : n ≤ m) (t : {t : ℝ // t ∈ Set.Ioo 0 (L n)}),
      i n t = i m ⟨t.1, ⟨t.2.1, lt_of_lt_of_le t.2.2 (hmono_chain hnm)⟩⟩ := by
    intro n0 m hnm t
    let Q : (k : ℕ) → n0 ≤ k → Prop := fun k h =>
      i n0 t = i k ⟨t.1, ⟨t.2.1, lt_of_lt_of_le t.2.2 (hmono_chain h)⟩⟩
    change Q m hnm
    refine Nat.le_induction (m := n0) (P := Q) ?base ?succ m hnm
    · exact congrArg (i n0) (by apply Subtype.ext; rfl)
    · intro k hk ih
      let el : {t : ℝ // t ∈ Set.Ioo 0 (L k)} :=
        ⟨t.1, ⟨t.2.1, lt_of_lt_of_le t.2.2 (hmono_chain hk)⟩⟩
      refine (ih.trans (hiAgree k el)).trans ?_
      apply congrArg (i (k + 1))
      apply Subtype.ext
      rfl
  -- well-definedness: two representatives with the same coordinate agree
  have e_eq_of : ∀ (a : ℝ) (pa : 0 < a) (n m : ℕ) (hn : a < L n) (hm : a < L m),
      i n ⟨a, ⟨pa, hn⟩⟩ = i m ⟨a, ⟨pa, hm⟩⟩ := by
    intro a pa n m hn hm
    by_cases hnm : n ≤ m
    · calc
        i n ⟨a, ⟨pa, hn⟩⟩ = i m ⟨a, ⟨pa, lt_of_lt_of_le hn (hmono_chain hnm)⟩⟩ := by
          simpa using hchain hnm ⟨a, ⟨pa, hn⟩⟩
        _ = i m ⟨a, ⟨pa, hm⟩⟩ := by
          apply congrArg (i m)
          apply Subtype.ext
          rfl
    · have hmn : m ≤ n := le_of_lt (lt_of_not_ge hnm)
      have hforward : i m ⟨a, ⟨pa, hm⟩⟩ = i n ⟨a, ⟨pa, hn⟩⟩ := by
        calc
          i m ⟨a, ⟨pa, hm⟩⟩ = i n ⟨a, ⟨pa, lt_of_lt_of_le hm (hmono_chain hmn)⟩⟩ := by
            simpa using hchain hmn ⟨a, ⟨pa, hm⟩⟩
          _ = i n ⟨a, ⟨pa, hn⟩⟩ := by
            apply congrArg (i n)
            apply Subtype.ext
            rfl
      exact hforward.symm
  -- inclusion of an interval (0, L n) into (0, S)
  let toA : ∀ n : ℕ, {t : ℝ // t ∈ Set.Ioo 0 (L n)} → A :=
    fun n t => ⟨t.1, ⟨t.2.1, lt_of_lt_of_le t.2.2 (hLleS n)⟩⟩
  have hcont_toA : ∀ n : ℕ, Continuous (toA n) := fun n =>
    Continuous.subtype_mk
      (show Continuous (fun t : {t : ℝ // t ∈ Set.Ioo 0 (L n)} => (t : ℝ)) from
        continuous_subtype_val)
      (fun t => ⟨t.2.1, lt_of_lt_of_le t.2.2 (hLleS n)⟩)
  -- the pasted map e : A → X
  let e : A → X := fun t =>
    i (Classical.choose (hexists t.1 t.2.2)) ⟨t.1, ⟨t.2.1, Classical.choose_spec (hexists t.1 t.2.2)⟩⟩
  have e_eq : ∀ (t : A) (n : ℕ) (ht : t.1 < L n), e t = i n ⟨t.1, ⟨t.2.1, ht⟩⟩ := by
    intro t n ht
    change i (Classical.choose (hexists t.1 t.2.2))
        ⟨t.1, ⟨t.2.1, Classical.choose_spec (hexists t.1 t.2.2)⟩⟩ = i n ⟨t.1, ⟨t.2.1, ht⟩⟩
    exact e_eq_of t.1 t.2.1 (Classical.choose (hexists t.1 t.2.2)) n
      (Classical.choose_spec (hexists t.1 t.2.2)) ht
  -- injectivity of e
  have heinj : Function.Injective e := by
    intro t u htu
    let nt : ℕ := Classical.choose (hexists t.1 t.2.2)
    let nu : ℕ := Classical.choose (hexists u.1 u.2.2)
    have hspec_t : t.1 < L nt := Classical.choose_spec (hexists t.1 t.2.2)
    have hspec_u : u.1 < L nu := Classical.choose_spec (hexists u.1 u.2.2)
    let k : ℕ := max nt nu
    have hkn : nt ≤ k := le_max_left nt nu
    have hku : nu ≤ k := le_max_right nt nu
    have htLk : t.1 < L k := lt_of_lt_of_le hspec_t (hmono_chain hkn)
    have huLk : u.1 < L k := lt_of_lt_of_le hspec_u (hmono_chain hku)
    have hmain : i k ⟨t.1, ⟨t.2.1, htLk⟩⟩ = i k ⟨u.1, ⟨u.2.1, huLk⟩⟩ := by
      exact (e_eq t k htLk).symm.trans (htu.trans (e_eq u k huLk))
    have hval : t.1 = u.1 := by
      simpa using congrArg Subtype.val (hiInj k hmain)
    exact Subtype.ext hval
  -- surjectivity of e
  have hesurj : Function.Surjective e := by
    intro x
    rcases hiCover x with ⟨n, t, ht⟩
    refine ⟨toA n t, ?_⟩
    have hE : e (toA n t) = i n ⟨(toA n t).1, ⟨(toA n t).2.1, t.2.2⟩⟩ := e_eq (toA n t) n t.2.2
    have hArg : (⟨(toA n t).1, ⟨(toA n t).2.1, t.2.2⟩⟩ : {t : ℝ // t ∈ Set.Ioo 0 (L n)}) = t := by
      apply Subtype.ext
      rfl
    exact hE.trans ((congrArg (i n) hArg).trans ht)
  -- openness of the pieces U n := {t : A | t.1 < L n}
  let U : ℕ → Set A := fun n => {t : A | t.1 < L n}
  have isOpen_U : ∀ n : ℕ, IsOpen (U n) := by
    intro n
    change IsOpen ((fun t : A => (t : ℝ)) ⁻¹' Set.Iio (L n))
    exact IsOpen.preimage continuous_subtype_val isOpen_Iio
  -- continuity of e (past the open cover {U n})
  have hcont_e : Continuous e := by
    refine continuous_of_cover_nhds (ι := ℕ) (s := U) ?_ ?_
    · intro t
      rcases hexists t.1 t.2.2 with ⟨n, hn⟩
      exact ⟨n, (isOpen_U n).mem_nhds hn⟩
    · intro n
      rw [continuousOn_iff_continuous_domRestrict]
      have hcont_R : Continuous (fun u : {t : A // t ∈ U n} =>
          i n ⟨(u : A).1, ⟨(u : A).2.1, u.2⟩⟩) := by
        refine (hiCont n).comp ?_
        apply Continuous.subtype_mk
        show Continuous (fun u : {t : A // t ∈ U n} => ((u : A) : ℝ))
        exact continuous_subtype_val.comp
          (continuous_subtype_val : Continuous (fun u : {t : A // t ∈ U n} => (u : A)))
      have hEq : (U n).domRestrict e = fun u : {t : A // t ∈ U n} =>
          i n ⟨(u : A).1, ⟨(u : A).2.1, u.2⟩⟩ := by
        funext u
        change e (u : A) = i n ⟨(u : A).1, ⟨(u : A).2.1, u.2⟩⟩
        exact e_eq (u : A) n u.2
      rw [hEq]
      exact hcont_R
  -- e is an open map
  have hopenmap : IsOpenMap e := by
    intro W hW
    have hcov : W = ⋃ n : ℕ, W ∩ U n := by
      ext t
      constructor
      · intro ht
        rw [mem_iUnion]
        rcases hexists t.1 t.2.2 with ⟨n, hn⟩
        exact ⟨n, ⟨ht, hn⟩⟩
      · intro ht
        rw [mem_iUnion] at ht
        rcases ht with ⟨n, htn⟩
        exact htn.1
    have himg : ∀ (W : Set A) (n : ℕ), e '' (W ∩ U n) = i n '' (toA n ⁻¹' W) := by
      intro W n
      ext y
      constructor
      · intro hy
        rcases hy with ⟨t, htm, hyt⟩
        rcases htm with ⟨htW, htU⟩
        refine ⟨⟨t.1, ⟨t.2.1, htU⟩⟩, ?_, ?_⟩
        · change toA n ⟨t.1, ⟨t.2.1, htU⟩⟩ ∈ W
          have hEq : toA n ⟨t.1, ⟨t.2.1, htU⟩⟩ = t := by
            apply Subtype.ext
            rfl
          simpa [hEq] using htW
        · exact (e_eq t n htU).symm.trans hyt
      · intro hy
        rcases hy with ⟨u, hu, hiu⟩
        refine ⟨toA n u, ⟨hu, u.2.2⟩, ?_⟩
        have hE : e (toA n u) = i n ⟨(toA n u).1, ⟨(toA n u).2.1, u.2.2⟩⟩ := e_eq (toA n u) n u.2.2
        have hArg : (⟨(toA n u).1, ⟨(toA n u).2.1, u.2.2⟩⟩ : {t : ℝ // t ∈ Set.Ioo 0 (L n)}) = u := by
          apply Subtype.ext
          rfl
        exact hE.trans ((congrArg (i n) hArg).trans hiu)
    rw [hcov, Set.image_iUnion]
    apply isOpen_iUnion
    intro n
    rw [himg W n]
    exact hiOpenMap n (toA n ⁻¹' W) (hW.preimage (hcont_toA n))
  -- assemble the homeomorphism
  let equiv : A ≃ X := Equiv.ofBijective e ⟨heinj, hesurj⟩
  exact ⟨equiv.toHomeomorphOfContinuousOpen hcont_e hopenmap⟩

end Commons.Topology.Exhaustion