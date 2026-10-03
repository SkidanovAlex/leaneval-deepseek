/-
# The third clause of [JZLA20, Proposition 5.1(2)]

[JZLA20, Proposition 5.1(2)] states, for `b ∈ D_{H,P}` with `b = ∑ b_k`, that the
`H`-complexities of the coefficients are bounded by `Tree_H(b)`, that the bound is attained at
most once, and — the clause proved here — that **if it is attained, then every `β ∈ Rat(E × H)`
realising the complexity of `b` lies in `Rat(E^×N) · t^n`.**

This last clause is what excludes the "single monomial" case `a = a_n t^n` in the proof of
[JZLA20, Theorem 6.1]: by [DHS04, Theorem 5.7] (`Rat.exists_source_subgroup_weak`) a realiser
`α ∈ Rat(K^×N)·t^n` of `a` has `source(α) ≤ K^×N`, whence `H ≤ N`, contradicting `H/N ≅ ℤ`.

## Structure of the proof

Let `β ∈ Rat(E × H)` with `Φ β = b` and `Tree β = Tree_H(b)`, and suppose that `b` is a single
monomial with coefficient at `k`.  Decompose `β` by `RatU.exists_decomp`:

* `β = ofGroup u`: writing `u = n·t^j` with `n ∈ N` (`Prop51Data.decomp`) and comparing the `k`-th
  coefficients of the two monomial series exhibiting `b` gives `j = k`, so that
  `β = ofGroup n · ofGroup (t^k)`;
* `β = y + z` (the "sum" case): the equality chain
  `Tree_H(b) ≤ Tree_H(Φy) + Tree_H(Φz) ≤ Tree y + Tree z = Tree β = Tree_H(b)` forces
  `Tree_H(Φy) = Tree y` and `Tree_H(Φz) = Tree z`, so both pieces are of strictly smaller
  complexity and the induction hypothesis applies to them: `y ∈ Rat(N)t^k` and `z ∈ Rat(N)t^k`
  (the index is pinned down by the same equality chain applied to the `k`-th coefficients);
* `β = y·z` (the "product" case): the analogous chain with `*` gives `Tree_H(Φy) = Tree y`,
  `Tree_H(Φz) = Tree z`; `mul_index` below shows that the coefficients of the two series realising
  `Φy` and `Φz` have a *unique* maximal coefficient each and that their indices add up to `k`;
* `β = y⋄` (the `⋄` case): `b = (Φy)⋄ ≠ 0` makes `Φy` a unit of `D_{H,P}`
  (`Prop51Data.ratOp_ne_zero`), hence `b = (Φy)⁻¹`; writing `b = a_k t^k` exhibits `a_k` as a unit
  of `P` and hence, by `Prop51Data.DN_inv_closed`, of `D_{N,P}`, so that
  `Φy = Φ(t^{-k})·a_k^{-1}`.  The coefficient of the realising series of `Φy` at index `-k` is then
  of full complexity `Tree_H(Φy)`, so the induction hypothesis gives `y ∈ Rat(N)t^{-k}`, and the
  rational axiom produces `β = y⋄ ∈ Rat(N)t^k`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Prop51
import Submission.Work.ORHughesFree.Prop51.ConclB
import Submission.Work.ORHughesFree.Prop51.conj
import Submission.Work.ORHughesFree.Prop51.coeff_zpowT
import Submission.Work.ORHughesFree.Prop51.ofGroup_t_pow
import Submission.Work.ORHughesFree.Prop51.treeH_ofGroup
import Submission.Work.ORHughesFree.Prop51.treeH_coeffToP_mul_ofAdd_le
import Submission.Work.ORHughesFree.Prop51.olt_dlog_coeffToP_mul_ofAdd
import Submission.Work.ORHughesFree.RatU.isWord_wid
import Submission.Work.ORHughesFree.RatU.exists_conj_ofSubgroup
import Submission.Work.ORHughesFree.RatU.exists_decomp
import Submission.Work.ORHughesFree.SkewLaurentSeries.eq_coeff_mul_zpowT
import Submission.Work.ORHughesFree.Prop51.prop51_case
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.Tree.olt_dlog_sum
import Submission.Work.ORHughesFree.Tree.log_mul
import Submission.Work.ORHughesFree.Tree.log_add
import Submission.Work.ORHughesFree.Tree.olt_dlog_of_lt_exp
import Submission.Work.ORHughesFree.Tree.exp_mono
import Submission.Work.ORHughesFree.SkewLaurentSeries.mul_apply_eq_single
import Submission.Work.ORHughesFree.SkewLaurentSeries.mul_apply_eq_single_right

set_option autoImplicit false

namespace Work.ORHughesFree.Prop51

open Work.ORHughesFree

variable {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
  [MulSemiringAction (Multiplicative ℤ) ↥DN]

/-! ### The index of a coefficient of maximal complexity of a product -/

/-- **The index lemma for products.**  Let `f`, `g` be series with the property that the maximal
coefficient complexity of `f` is `≤ T₁` and that the bound `T₁` is attained at most once (and
similarly for `g` and `T₂`), and suppose that some coefficient of the product `f * g` has complexity
exactly `T₁ * T₂`.  Then the bound `T₁` *is* attained by `f` (at some `i₀`), the bound `T₂` *is*
attained by `g` (at some `j₀`), `f` is a monomial at `i₀`, `g` is a monomial at `j₀`, and
`i₀ + j₀ = n`.

The existence of `i₀` resp. `j₀` is by contradiction: if every coefficient of `f` were strictly
below `T₁`, then `dlog` of every coefficient is strictly below `some A` (`log T₁ = some A`), and the
three estimates `treeH_coeffToP_mul_ofAdd_le`, `ole_dlog_mul`, `ole_dlog_add` propagate this
strictness through the skew convolution product (`olt_dlog_coeffToP_mul_ofAdd`,
`olt_dlog_sum`), giving `treeH ((f*g).1 n) < T₁*T₂`. -/
theorem mul_index {d : Prop51Data Γ P DN} {T₁ T₂ : Tree} (hT₁ : T₁ ≠ 0) (hT₂ : T₂ ≠ 0)
    (hw₁ : Tree.wid T₁ = 1) (hw₂ : Tree.wid T₂ = 1)
    {f g : SkewLaurentSeries ↥DN}
    (hfb : ∀ k : ℤ, Tree.le (d.treeH (d.coeffToP (f.1 k))) T₁)
    (hfm : ∀ k : ℤ, d.treeH (d.coeffToP (f.1 k)) = T₁ → ∀ j : ℤ, j ≠ k → f.1 j = 0)
    (hgb : ∀ k : ℤ, Tree.le (d.treeH (d.coeffToP (g.1 k))) T₂)
    (hgm : ∀ k : ℤ, d.treeH (d.coeffToP (g.1 k)) = T₂ → ∀ j : ℤ, j ≠ k → g.1 j = 0)
    {n : ℤ} (hn : d.treeH (d.coeffToP ((f * g).1 n)) = T₁ * T₂) :
    ∃ (i₀ j₀ : ℤ), i₀ + j₀ = n ∧ (∀ j : ℤ, j ≠ i₀ → f.1 j = 0) ∧
      (∀ i : ℤ, i ≠ j₀ → g.1 i = 0) ∧
      d.treeH (d.coeffToP (f.1 i₀)) = T₁ ∧ d.treeH (d.coeffToP (g.1 j₀)) = T₂ := by
  obtain ⟨A₀, hA₀⟩ := (Tree.log_spec T₁).2.2 hT₁
  obtain ⟨B₀, hB₀⟩ := (Tree.log_spec T₂).2.2 hT₂
  have hprod : T₁ * T₂ ≠ 0 := by
    rw [Tree.eq_exp_log_of_wid_eq_one hA₀ hw₁, Tree.eq_exp_log_of_wid_eq_one hB₀ hw₂,
      ← Tree.exp_add]
    exact Tree.exp_ne_zero _
  have hn0 : d.coeffToP ((f * g).1 n) ≠ 0 := fun h0 => by
    rw [h0, (d.treeH_eq_zero_iff d.DH.zero_mem).mpr rfl] at hn
    exact hprod hn.symm
  have hfgne : (f * g).1 n ≠ 0 := fun h0 => hn0 (by rw [h0]; rfl)
  -- the `f`-side: `T₁` is attained
  have hfmax : ∃ i : ℤ, d.treeH (d.coeffToP (f.1 i)) = T₁ := by
    by_contra hcon
    have hflt : ∀ i : ℤ, Tree.lt (d.treeH (d.coeffToP (f.1 i))) T₁ :=
      fun i => Tree.lt_of_le_of_ne (hfb i) (fun h => hcon ⟨i, h⟩)
    obtain ⟨A, hA⟩ := (Tree.log_spec T₁).2.2 hT₁
    have hT₁e : T₁ = Tree.exp A := Tree.eq_exp_log_of_wid_eq_one hA hw₁
    have hfO : ∀ i : ℤ, Tree.Olt (Tree.dlog (d.treeH (d.coeffToP (f.1 i)))) (some A) :=
      fun i => Tree.olt_dlog_of_lt_exp (by rw [← hT₁e]; exact hflt i)
    by_cases hgmax : ∃ j : ℤ, d.treeH (d.coeffToP (g.1 j)) = T₂
    · -- `g` is a monomial, `f` has all coefficients strictly below `T₁`
      obtain ⟨j₀, hj₀⟩ := hgmax
      have hgmono : ∀ j : ℤ, j ≠ j₀ → g.1 j = 0 := fun j hj => hgm j₀ hj₀ j hj
      have hlt : Tree.lt (d.treeH (d.coeffToP ((f * g).1 n))) (T₁ * T₂) := by
        rw [SkewLaurentSeries.mul_apply_eq_single_right f g j₀ n hgmono]
        have hbase := treeH_coeffToP_mul_ofAdd_le d f g n (n - j₀)
        rw [show n - (n - j₀) = j₀ by omega] at hbase
        refine Tree.lt_of_le_of_lt' hbase ?_
        rw [hj₀]
        exact Tree.lt_mul_right (hflt (n - j₀)) hT₂
      rw [hn] at hlt
      exact Tree.lt_irrefl hlt
    · -- both factors have all coefficients strictly below their bounds
      have hglt : ∀ j : ℤ, Tree.lt (d.treeH (d.coeffToP (g.1 j))) T₂ :=
        fun j => Tree.lt_of_le_of_ne (hgb j) (fun h => hgmax ⟨j, h⟩)
      obtain ⟨B, hB⟩ := (Tree.log_spec T₂).2.2 hT₂
      have hT₂e : T₂ = Tree.exp B := Tree.eq_exp_log_of_wid_eq_one hB hw₂
      have hgO : ∀ j : ℤ, Tree.Olt (Tree.dlog (d.treeH (d.coeffToP (g.1 j)))) (some B) :=
        fun j => Tree.olt_dlog_of_lt_exp (by rw [← hT₂e]; exact hglt j)
      have hAB : Tree.dlog (T₁ * T₂) = some (A + B) := Tree.log_mul hA hB
      have hterm : ∀ k ∈ Finset.Icc (SkewLaurentSeries.lo f) (n - SkewLaurentSeries.lo g),
          Tree.Olt (Tree.dlog (d.treeH (d.coeffToP
            (f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k)))))) (some (A + B)) :=
        fun k _ => olt_dlog_coeffToP_mul_ofAdd d f g n k (hfO k) (hgO (n - k))
      have hsum := Tree.olt_dlog_sum
        (Finset.Icc (SkewLaurentSeries.lo f) (n - SkewLaurentSeries.lo g))
        (fun k => d.treeH (d.coeffToP (f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k)))))
        (A + B) hterm
      have hle := treeH_le_sum
        (Finset.Icc (SkewLaurentSeries.lo f) (n - SkewLaurentSeries.lo g))
        (fun k => d.coeffToP (f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k))))
        (fun k _ => d.coeffToP_mem _)
      have hcoeff : d.coeffToP ((f * g).1 n) =
          ∑ k ∈ Finset.Icc (SkewLaurentSeries.lo f) (n - SkewLaurentSeries.lo g),
            d.coeffToP (f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k))) := by
        rw [SkewLaurentSeries.mul_apply]
        exact map_sum (Subring.subtype DN) _ _
      have h1 : Tree.Ole (Tree.dlog (d.treeH (d.coeffToP ((f * g).1 n))))
          (Tree.dlog (∑ k ∈ Finset.Icc (SkewLaurentSeries.lo f) (n - SkewLaurentSeries.lo g),
            d.treeH (d.coeffToP (f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k)))))) := by
        rw [hcoeff]
        exact Tree.ole_dlog_of_le hle
      have h2 : Tree.Olt (Tree.dlog (d.treeH (d.coeffToP ((f * g).1 n)))) (some (A + B)) :=
        Tree.ole_olt_trans h1 hsum
      have hlt : Tree.lt (d.treeH (d.coeffToP ((f * g).1 n))) (T₁ * T₂) :=
        Tree.lt_of_olt_dlog (x := d.treeH (d.coeffToP ((f * g).1 n))) (y := T₁ * T₂)
          (by rw [hAB]; exact h2)
      rw [hn] at hlt
      exact Tree.lt_irrefl hlt
  obtain ⟨i₀, hi₀⟩ := hfmax
  have hfmono : ∀ j : ℤ, j ≠ i₀ → f.1 j = 0 := fun j hj => hfm i₀ hi₀ j hj
  -- the `g`-side: `T₂` is attained
  have hgmax : ∃ j : ℤ, d.treeH (d.coeffToP (g.1 j)) = T₂ := by
    by_contra hcon
    have hglt : ∀ j : ℤ, Tree.lt (d.treeH (d.coeffToP (g.1 j))) T₂ :=
      fun j => Tree.lt_of_le_of_ne (hgb j) (fun h => hcon ⟨j, h⟩)
    obtain ⟨B, hB⟩ := (Tree.log_spec T₂).2.2 hT₂
    have hT₂e : T₂ = Tree.exp B := Tree.eq_exp_log_of_wid_eq_one hB hw₂
    have hgO : ∀ j : ℤ, Tree.Olt (Tree.dlog (d.treeH (d.coeffToP (g.1 j)))) (some B) :=
      fun j => Tree.olt_dlog_of_lt_exp (by rw [← hT₂e]; exact hglt j)
    have hlt : Tree.lt (d.treeH (d.coeffToP ((f * g).1 n))) (T₁ * T₂) := by
      rw [SkewLaurentSeries.mul_apply_eq_single f g i₀ n hfmono]
      have hbase := treeH_coeffToP_mul_ofAdd_le d f g n i₀
      refine Tree.lt_of_le_of_lt' hbase ?_
      rw [hi₀]
      exact Tree.lt_mul_left (hglt (n - i₀)) hT₁
    rw [hn] at hlt
    exact Tree.lt_irrefl hlt
  obtain ⟨j₀, hj₀⟩ := hgmax
  have hgmono : ∀ j : ℤ, j ≠ j₀ → g.1 j = 0 := fun j hj => hgm j₀ hj₀ j hj
  refine ⟨i₀, j₀, ?_, hfmono, hgmono, hi₀, hj₀⟩
  by_contra hne
  have hzero : (f * g).1 n = 0 := by
    rw [SkewLaurentSeries.mul_apply_eq_single f g i₀ n hfmono]
    have hnj : n - i₀ ≠ j₀ := fun h => hne (by omega)
    rw [hgmono (n - i₀) hnj, smul_zero, mul_zero]
  exact hfgne hzero

/-! ### The coefficient of a power of `t` times a constant series -/

/-- The `m`-th coefficient of `t^j · coeff a` is `τ^j a` when `m = j` and `0` otherwise. -/
theorem zpowT_mul_coeff_apply {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (j m : ℤ) (a : A) :
    ((↑((skewLaurentSeriesT A) ^ j) : SkewLaurentSeries A) * skewLaurentCoeff A a).1 m =
      if m = j then (Multiplicative.ofAdd j) • a else 0 := by
  rw [skewLaurentSeriesT_zpow_mul_coeff j a]
  exact coeff_zpowT ((Multiplicative.ofAdd j) • a) j m

/-! ### The main statement -/

/-- **The third clause of [JZLA20, Proposition 5.1(2)].**

Let `b ∈ D_{H,P}` be realised by the series `f ∈ D_{N,P}((t;τ))` whose coefficient of maximal
complexity sits at the index `k`, and assume that every non-zero element of `D_{H,P}` of
`H`-complexity strictly below `Tree_H(a)` satisfies the strengthened conclusion `Prop51ConclP`
(the induction hypothesis of [JZLA20, Proposition 5.1]).  Then every `β ∈ Rat(E × H)` with
`Φ β = b` and `Tree β = Tree_H(b)` lies in `Rat(E^×N)·t^k`. -/
theorem prop51_mono (d : Prop51Data Γ P DN) {a b : P} {f : SkewLaurentSeries ↥DN}
    (hf : d.laurentEmbed f = b)
    (hbmem : b ∈ d.DH) (hbal : Tree.le (d.treeH b) (d.treeH a))
    (hbound : ∀ k : ℤ, Tree.le (d.treeH (d.coeffToP (f.1 k))) (d.treeH b))
    (hsingle : ∀ k : ℤ, d.treeH (d.coeffToP (f.1 k)) = d.treeH b → ∀ j : ℤ, j ≠ k → f.1 j = 0)
    (hsmall : ∀ b' ∈ d.DH, Tree.lt (d.treeH b') (d.treeH a) → Prop51ConclP d b')
    {k : ℤ} (hk : d.treeH (d.coeffToP (f.1 k)) = d.treeH b) :
    Prop51Mono d b k := by
  intro β hβ htree
  by_cases hb0 : b = 0
  · have hT : Rat.treeOfRat Γ β = (0 : Tree) := by
      rw [htree, hb0]
      exact (d.treeH_eq_zero_iff d.DH.zero_mem).mpr rfl
    have hβ0 : β = 0 := (Rat.treeOfRat_eq_zero_iff Γ β).mp hT
    exact ⟨0, by rw [hβ0, map_zero, zero_mul]⟩
  have hTb : d.treeH b ≠ 0 := d.treeH_ne_zero hbmem hb0
  have hfk : f.1 k ≠ 0 := by
    intro h0
    have hc : d.coeffToP (f.1 k) = 0 := by rw [h0]; rfl
    exact hTb (hk ▸ (by rw [hc]; exact (d.treeH_eq_zero_iff d.DH.zero_mem).mpr rfl))
  have hβne : β ≠ 0 := by
    intro h0
    rw [h0, Rat.treeOfRat_zero] at htree
    exact hTb htree.symm
  rcases RatU.exists_decomp β hβne with hgrp | hprod | hsum | hrat
  · -- the base case: `β` is the image of a group element
    obtain ⟨u, hu⟩ := hgrp
    obtain ⟨n, j, hn, huj⟩ := d.decomp u
    have hbu : d.Φ (RatU.ofGroup u) = b := by rw [← hβ, hu]
    have key : d.laurentEmbed (skewLaurentCoeff ↥DN ⟨d.Φ (RatU.ofGroup n), d.Φ_N n hn⟩ *
        ↑((skewLaurentSeriesT ↥DN) ^ j)) = d.laurentEmbed f := by
      rw [map_mul, d.laurentEmbed_coeff, ← Φ_ofGroup_t_zpow d j, ← map_mul, ← RatU.ofGroup_mul]
      rw [← huj, hbu, hf]
    have hfj : f = skewLaurentCoeff ↥DN ⟨d.Φ (RatU.ofGroup n), d.Φ_N n hn⟩ *
        ↑((skewLaurentSeriesT ↥DN) ^ j) := (d.laurentEmbed_injective key).symm
    have hjk : j = k := by
      have h0 : f.1 k = (if k = j then (⟨d.Φ (RatU.ofGroup n), d.Φ_N n hn⟩ : ↥DN) else 0) := by
        rw [hfj, coeff_zpowT]
      by_contra hne
      rw [if_neg (fun h => hne h.symm)] at h0
      exact hfk h0
    refine ⟨RatU.ofGroup ⟨n, hn⟩, ?_⟩
    rw [hu, Rat.ofSubgroup_ofGroup d.N ⟨n, hn⟩, ← RatU.ofGroup_mul, ← hjk, huj]
  · -- the product case
    obtain ⟨y, z, hyz, hyw, hzw, hylt, hzlt⟩ := hprod
    have hy0 : y ≠ 0 := RatU.isWord_ne_zero' hyw
    have hz0 : z ≠ 0 := RatU.isWord_ne_zero' hzw
    have hbce : d.Φ y * d.Φ z = b := by rw [← map_mul, ← hyz, hβ]
    have hT₁ : d.treeH (d.Φ y) ≠ 0 := fun h0 =>
      hb0 (by rw [← hbce, (d.treeH_eq_zero_iff (d.map_mem y)).mp h0, zero_mul])
    have hT₂ : d.treeH (d.Φ z) ≠ 0 := fun h0 =>
      hb0 (by rw [← hbce, (d.treeH_eq_zero_iff (d.map_mem z)).mp h0, mul_zero])
    have hchain : Tree.le (d.treeH b) (d.treeH (d.Φ y) * d.treeH (d.Φ z)) := by
      rw [← hbce]
      exact treeH_le_mul d (d.map_mem y) (d.map_mem z)
    have hyzT : Rat.treeOfRat Γ y * Rat.treeOfRat Γ z = d.treeH b := by
      rw [← Rat.treeOfRat_mul, ← hyz, htree]
    have heq : d.treeH (d.Φ y) * d.treeH (d.Φ z)
        = Rat.treeOfRat Γ y * Rat.treeOfRat Γ z :=
      Tree.le_antisymm (Tree.le_mul (d.treeH_le_treeOfRat y) (d.treeH_le_treeOfRat z))
        (hyzT ▸ hchain)
    obtain ⟨hcy, hcz⟩ :=
      (Tree.le_mul_eq hT₁ hT₂ (d.treeH_le_treeOfRat y) (d.treeH_le_treeOfRat z)).mp heq
    have hw₁ : Tree.wid (d.treeH (d.Φ y)) = 1 := by
      rw [hcy]; exact RatU.isWord_wid hyw
    have hw₂ : Tree.wid (d.treeH (d.Φ z)) = 1 := by
      rw [hcz]; exact RatU.isWord_wid hzw
    have hyl' : Tree.lt (Rat.treeOfRat Γ y) (Rat.treeOfRat Γ y * Rat.treeOfRat Γ z) := by
      have h2 := hylt
      rw [hyz, Rat.treeOfRat_mul] at h2
      exact h2
    have hzl' : Tree.lt (Rat.treeOfRat Γ z) (Rat.treeOfRat Γ y * Rat.treeOfRat Γ z) := by
      have h2 := hzlt
      rw [hyz, Rat.treeOfRat_mul] at h2
      exact h2
    have hly : Tree.lt (d.treeH (d.Φ y)) (d.treeH a) := by
      refine lt_of_lt_of_le_Tree ?_ hbal
      rw [hcy, ← hyzT]
      exact hyl'
    have hlz : Tree.lt (d.treeH (d.Φ z)) (d.treeH a) := by
      refine lt_of_lt_of_le_Tree ?_ hbal
      rw [hcz, ← hyzT]
      exact hzl'
    obtain ⟨g, hg, hgb, hgm, hgmono⟩ := hsmall (d.Φ y) (d.map_mem y) hly
    obtain ⟨g', hg', hg'b, hg'm, hg'mono⟩ := hsmall (d.Φ z) (d.map_mem z) hlz
    have hfprod : g * g' = f := by
      apply d.laurentEmbed_injective
      rw [map_mul, hg, hg', ← map_mul, ← hyz, hβ, hf]
    have hn : d.treeH (d.coeffToP ((g * g').1 k)) = d.treeH (d.Φ y) * d.treeH (d.Φ z) := by
      rw [hfprod, hk, heq, hyzT]
    obtain ⟨i₀, j₀, hij, hgm0, hgm1, hgi, hgj⟩ :=
      mul_index (d := d) hT₁ hT₂ hw₁ hw₂ hgb hgm hg'b hg'm hn
    obtain ⟨y', hy'⟩ := hgmono i₀ hgi y rfl hcy.symm
    obtain ⟨z', hz'⟩ := hg'mono j₀ hgj z rfl hcz.symm
    obtain ⟨z'', hz''⟩ := RatU.exists_conj_ofSubgroup d.N d.t d.N_conj i₀ z'
    refine ⟨y' * z'', ?_⟩
    have hTk : RatU.ofGroup (d.t ^ k) =
        RatU.ofGroup (d.t ^ i₀) * RatU.ofGroup (d.t ^ j₀) := by
      rw [← hij, zpow_add, RatU.ofGroup_mul]
    rw [hyz, ← hy', ← hz', map_mul, hTk,
      show (RatU.ofSubgroup d.N y' * RatU.ofSubgroup d.N z'') *
            (RatU.ofGroup (d.t ^ i₀) * RatU.ofGroup (d.t ^ j₀)) =
          ((RatU.ofSubgroup d.N y' * RatU.ofSubgroup d.N z'') * RatU.ofGroup (d.t ^ i₀)) *
            RatU.ofGroup (d.t ^ j₀) from (mul_assoc _ _ _).symm,
      mul_assoc (RatU.ofSubgroup d.N y') (RatU.ofSubgroup d.N z'') (RatU.ofGroup (d.t ^ i₀)),
      ← hz'']
    noncomm_ring
  · -- the sum case
    obtain ⟨y, z, hyz, hy0, hz0, hylt, hzlt⟩ := hsum
    have hbce : d.Φ y + d.Φ z = b := by rw [← map_add, ← hyz, hβ]
    have hchain : Tree.le (d.treeH b) (d.treeH (d.Φ y) + d.treeH (d.Φ z)) := by
      rw [← hbce]
      exact treeH_le_add d (d.map_mem y) (d.map_mem z)
    have hyzT : Rat.treeOfRat Γ y + Rat.treeOfRat Γ z = d.treeH b := by
      rw [← Rat.treeOfRat_add, ← hyz, htree]
    have heq : d.treeH (d.Φ y) + d.treeH (d.Φ z)
        = Rat.treeOfRat Γ y + Rat.treeOfRat Γ z :=
      Tree.le_antisymm (Tree.le_add (d.treeH_le_treeOfRat y) (d.treeH_le_treeOfRat z))
        (hyzT ▸ hchain)
    obtain ⟨hcy, hcz⟩ :=
      (Tree.le_add_eq (d.treeH_le_treeOfRat y) (d.treeH_le_treeOfRat z)).mp heq
    have hbcz : d.treeH (d.Φ y) + d.treeH (d.Φ z) = d.treeH b := by rw [heq, hyzT]
    have hly : Tree.lt (d.treeH (d.Φ y)) (d.treeH a) := by
      refine lt_of_lt_of_le_Tree ?_ hbal
      rw [hcy, ← hyzT, ← Rat.treeOfRat_add]
      exact RatU.tree_lt_add_left hz0
    have hlz : Tree.lt (d.treeH (d.Φ z)) (d.treeH a) := by
      refine lt_of_lt_of_le_Tree ?_ hbal
      rw [hcz, ← hyzT, ← Rat.treeOfRat_add]
      exact RatU.tree_lt_add_right hy0
    obtain ⟨g, hg, hgb, hgm, hgmono⟩ := hsmall (d.Φ y) (d.map_mem y) hly
    obtain ⟨g', hg', hg'b, hg'm, hg'mono⟩ := hsmall (d.Φ z) (d.map_mem z) hlz
    have hfsum : g + g' = f := by
      apply d.laurentEmbed_injective
      rw [map_add, hg, hg', ← map_add, ← hyz, hβ, hf]
    have hk' : d.treeH (d.coeffToP ((g + g').1 k)) = d.treeH b := by
      rw [hfsum]; exact hk
    rw [SkewLaurentSeries.add_apply] at hk'
    have hk'' : d.treeH (d.coeffToP (g.1 k) + d.coeffToP (g'.1 k)) = d.treeH b := by
      have hce : d.coeffToP (g.1 k) + d.coeffToP (g'.1 k) = d.coeffToP (g.1 k + g'.1 k) := rfl
      rw [hce]; exact hk'
    have hbk : Tree.le (d.treeH (d.coeffToP (g.1 k)) + d.treeH (d.coeffToP (g'.1 k)))
        (d.treeH (d.Φ y) + d.treeH (d.Φ z)) := Tree.le_add (hgb k) (hg'b k)
    have heqk : d.treeH (d.coeffToP (g.1 k)) + d.treeH (d.coeffToP (g'.1 k))
        = d.treeH (d.Φ y) + d.treeH (d.Φ z) := by
      refine Tree.le_antisymm hbk ?_
      rw [hbcz, ← hk'']
      exact treeH_le_add d (d.coeffToP_mem _) (d.coeffToP_mem _)
    obtain ⟨hgk, hg'k⟩ := (Tree.le_add_eq (hgb k) (hg'b k)).mp heqk
    obtain ⟨y', hy'⟩ := hgmono k hgk y rfl hcy.symm
    obtain ⟨z', hz'⟩ := hg'mono k hg'k z rfl hcz.symm
    exact ⟨y' + z', by rw [hyz, map_add, add_mul, hy', hz']⟩
  · -- the `⋄` case
    obtain ⟨y, hy, hylt⟩ := hrat
    have hy0 : y ≠ 0 := by
      intro h0
      exact hβne (by rw [hy, h0, (RatU.rational (U := Γ)).ratOp_zero])
    have hc : d.Φ (RatU.rational.ratOp y) = b := by rw [← hβ, hy]
    have hbop : b = ((d.rDH.ratOp (⟨d.Φ y, d.map_mem y⟩ : ↥d.DH)) : P) := by
      rw [← hc]
      change (((d.Φ.codRestrict d.DH d.map_mem) (RatU.rational.ratOp y) : ↥d.DH) : P) = _
      rw [d.Φ_rat.map_rat]
      rfl
    have hop0 : ((d.rDH.ratOp (⟨d.Φ y, d.map_mem y⟩ : ↥d.DH)) : P) ≠ 0 := by
      rw [← hbop]; exact hb0
    have hunit : IsUnit (⟨d.Φ y, d.map_mem y⟩ : ↥d.DH) :=
      d.ratOp_ne_zero _ (fun h0 => hop0 (by rw [h0]; rfl))
    have hcb : d.Φ y * b = 1 := by
      rw [hbop]
      simpa using congrArg Subtype.val
        (d.ratOp_of_isUnit (⟨d.Φ y, d.map_mem y⟩ : ↥d.DH) hunit)
    have hcv : IsUnit (d.Φ y) := hunit.map (Subring.subtype d.DH)
    set U : Pˣ := hcv.unit with hU
    have hUval : (↑U : P) = d.Φ y := by rw [hU]; exact hcv.unit_spec
    have hbc : b = ↑(U⁻¹) := by
      have h2 : (↑U : P) * b = 1 := by rw [hUval]; exact hcb
      calc b = (↑(U⁻¹) * ↑U) * b := by rw [Units.inv_mul, one_mul]
        _ = ↑(U⁻¹) * (↑U * b) := by rw [mul_assoc]
        _ = ↑(U⁻¹) := by rw [h2, mul_one]
    have hbC : b * d.Φ y = 1 := by
      rw [hbc, ← hUval]
      exact Units.inv_mul U
    have hbunit : IsUnit b := ⟨⟨b, d.Φ y, hbC, hcb⟩, rfl⟩
    -- the two-sided inverse of `Φ (t^k)`
    have hTTi : d.Φ (RatU.ofGroup (d.t ^ k)) * d.Φ (RatU.ofGroup (d.t ^ (-k))) = 1 := by
      rw [← map_mul, ← RatU.ofGroup_mul, ← zpow_add, add_neg_cancel, zpow_zero,
        RatU.ofGroup_one, map_one]
    have hTiT : d.Φ (RatU.ofGroup (d.t ^ (-k))) * d.Φ (RatU.ofGroup (d.t ^ k)) = 1 := by
      rw [← map_mul, ← RatU.ofGroup_mul, ← zpow_add, neg_add_cancel, zpow_zero,
        RatU.ofGroup_one, map_one]
    let Uk : Pˣ := ⟨d.Φ (RatU.ofGroup (d.t ^ k)), d.Φ (RatU.ofGroup (d.t ^ (-k))), hTTi, hTiT⟩
    have hUk : (↑Uk : P) = d.Φ (RatU.ofGroup (d.t ^ k)) := rfl
    -- `b = a_k · Φ(t^k)`, so `a_k` is a unit
    have hbk : b = d.coeffToP (f.1 k) * d.Φ (RatU.ofGroup (d.t ^ k)) := by
      have hfm := SkewLaurentSeries.eq_coeff_mul_zpowT f k (hsingle k hk)
      calc b = d.laurentEmbed f := hf.symm
        _ = d.laurentEmbed (skewLaurentCoeff ↥DN (f.1 k) *
              ↑((skewLaurentSeriesT ↥DN) ^ k)) := congrArg d.laurentEmbed hfm
        _ = d.coeffToP (f.1 k) * d.Φ (RatU.ofGroup (d.t ^ k)) := by
              rw [map_mul, d.laurentEmbed_coeff, ← Φ_ofGroup_t_zpow d k]
              rfl
    have hbk' : b = d.coeffToP (f.1 k) * ↑Uk := by rw [hbk, hUk]
    have hakunit : IsUnit (d.coeffToP (f.1 k)) := by
      have h1 : d.coeffToP (f.1 k) = b * ↑(Uk⁻¹) := by
        rw [hbk', mul_assoc, Units.mul_inv, mul_one]
      rw [h1]
      exact hbunit.mul (Uk⁻¹).isUnit
    obtain ⟨v, hv, hv1, hv2⟩ := d.DN_inv_closed (d.coeffToP (f.1 k)) (f.1 k).2 hakunit
    -- `Φ y = Φ (t^{-k}) · a_k⁻¹`
    have hCA : d.Φ y * d.coeffToP (f.1 k) = d.Φ (RatU.ofGroup (d.t ^ (-k))) := by
      have hstep : d.Φ y * d.coeffToP (f.1 k) =
          (d.Φ y * d.coeffToP (f.1 k)) *
            (d.Φ (RatU.ofGroup (d.t ^ k)) * d.Φ (RatU.ofGroup (d.t ^ (-k)))) := by
        rw [hTTi, mul_one]
      rw [hstep, ← mul_assoc,
        mul_assoc (d.Φ y) (d.coeffToP (f.1 k)) (d.Φ (RatU.ofGroup (d.t ^ k))),
        ← hbk, hcb, one_mul]
    have hceq : d.Φ y = d.Φ (RatU.ofGroup (d.t ^ (-k))) * v := by
      have hstep : d.Φ y = d.Φ y * (d.coeffToP (f.1 k) * v) := by rw [hv1, mul_one]
      rw [hstep, ← mul_assoc, hCA]
    -- the complexity of `Φ y` is that of its realiser
    have hcy : d.treeH (d.Φ y) = Rat.treeOfRat Γ y := by
      refine Tree.le_antisymm (d.treeH_le_treeOfRat y) ?_
      have h1 : Tree.le (Tree.exp (Tree.exp (d.treeH (d.Φ y))))
          (Tree.exp (Tree.exp (Rat.treeOfRat Γ y))) :=
        Tree.exp_le_exp (Tree.exp_le_exp (d.treeH_le_treeOfRat y))
      have h2 : Tree.le (d.treeH b) (Tree.exp (Tree.exp (d.treeH (d.Φ y)))) := by
        rw [hbop]
        exact treeH_ratOp_le d (d.map_mem y)
      have h3 : Tree.exp (Tree.exp (Rat.treeOfRat Γ y)) = d.treeH b := by
        rw [← Rat.treeOfRat_rat_rational hy0, ← hy, htree]
      have h4 : Tree.le (Tree.exp (Tree.exp (Rat.treeOfRat Γ y)))
          (Tree.exp (Tree.exp (d.treeH (d.Φ y)))) := by
        rw [h3]; exact h2
      exact Tree.le_of_exp_le_exp
        (Tree.le_of_exp_le_exp (Or.inl (Tree.le_antisymm h4 h1)))
    have hlcy : Tree.lt (d.treeH (d.Φ y)) (d.treeH a) := by
      rw [hcy]
      refine lt_of_lt_of_le_Tree ?_ hbal
      rw [← htree]
      exact hylt
    obtain ⟨g, hg, hgb, hgm, hgmono⟩ := hsmall (d.Φ y) (d.map_mem y) hlcy
    -- the realising series of `Φ y` is `t^{-k} · coeff a_k⁻¹`
    have hgeq : g = (↑((skewLaurentSeriesT ↥DN) ^ (-k)) : SkewLaurentSeries ↥DN) *
        skewLaurentCoeff ↥DN (⟨v, hv⟩ : ↥DN) := by
      apply d.laurentEmbed_injective
      rw [hg, map_mul, d.laurentEmbed_coeff, ← Φ_ofGroup_t_zpow d (-k), hceq]
    have hgcoeff : d.treeH (d.coeffToP (g.1 (-k))) = d.treeH (d.Φ y) := by
      have hcoef : g.1 (-k) = (Multiplicative.ofAdd (-k)) • (⟨v, hv⟩ : ↥DN) := by
        rw [hgeq, zpowT_mul_coeff_apply, if_pos rfl]
      rw [hcoef, conj d (-k) (⟨v, hv⟩ : ↥DN), treeH_conj_eq d (-k) (d.coeffToP_mem _)]
      refine Tree.le_antisymm ?_ ?_
      · have hv_eq : d.Φ (RatU.ofGroup (d.t ^ k)) * d.Φ y = v := by
          rw [hceq, ← mul_assoc, hTTi, one_mul]
        have hEq : d.treeH (d.coeffToP (⟨v, hv⟩ : ↥DN)) =
            d.treeH (d.Φ (RatU.ofGroup (d.t ^ k)) * d.Φ y) := by
          rw [hv_eq]; rfl
        rw [hEq]
        exact Tree.le_trans (treeH_le_mul d (d.map_mem _) (d.map_mem y))
          (by rw [treeH_ofGroup d (d.t ^ k), one_mul]; exact Tree.le_refl _)
      · have hEq : d.treeH (d.Φ y) =
            d.treeH (d.Φ (RatU.ofGroup (d.t ^ (-k))) * d.coeffToP (⟨v, hv⟩ : ↥DN)) := by
          rw [hceq]; rfl
        rw [hEq]
        exact Tree.le_trans (treeH_le_mul d (d.map_mem _) (d.coeffToP_mem _))
          (by rw [treeH_ofGroup d (d.t ^ (-k)), one_mul]; exact Tree.le_refl _)
    obtain ⟨y', hy'⟩ := hgmono (-k) hgcoeff y rfl hcy.symm
    obtain ⟨y'', hy''⟩ := RatU.exists_conj_ofSubgroup d.N d.t d.N_conj k (RatU.rational.ratOp y')
    refine ⟨y'', ?_⟩
    have hrat : RatU.rational.ratOp (RatU.ofSubgroup d.N y' * RatU.ofGroup (d.t ^ (-k))) =
        RatU.ofGroup ((d.t ^ (-k))⁻¹) * RatU.rational.ratOp (RatU.ofSubgroup d.N y') := by
      have h := RatU.ofGroup_mul_ratOp ((d.t ^ (-k))⁻¹) (RatU.ofSubgroup d.N y')
      rw [inv_inv] at h
      exact h.symm
    have hmap : RatU.rational.ratOp (RatU.ofSubgroup d.N y') =
        RatU.ofSubgroup d.N (RatU.rational.ratOp y') := by
      have h := (RatU.ofSubgroup_isHom d.N).map_rat y'
      rw [RatU.restrictScalars_ratOp] at h
      exact h.symm
    rw [hy, ← hy', hrat, show (d.t ^ (-k))⁻¹ = d.t ^ k from by rw [← zpow_neg, neg_neg], hmap]
    exact hy''.symm

end Work.ORHughesFree.Prop51
