import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.lemma24
import Submission.Work.BG.lemma33Leaf
import Submission.Work.BG.lemma34Leaf
import Submission.Work.BG.L41Aux
import Submission.Work.BG.l41Vi
import Submission.Work.BG.l41Deriv
import Submission.Work.BG.l41Shape
-- (import Submission.Work.BG.l41Shape added when the delegated lemma lands)

/-!
# Area BG: Bender–Glauberman 1981, Lemma 4.1 (`Work.GW2.C16.Lemma41Prop`), §4 pp. 211–213

For a `BGData` `D` with `D.n = 2` (`|S| = 4`) and a compatible `Sec2Ctx` `C`, Lemma 4.1
says: for `χ ∈ ±Irr(G)` with `𝒮'(χ) ≠ ∅`,

* `|𝒮'(χ)| = 1` or `3`;
* `χ(t) = Σ_{ν ∈ 𝒮'(χ)} (χ, δ_ν) ν(1)`;
* `χ(1)` is odd,

where `δ_ν = (ν - λ₂ν)* = ind C (ν - λ₂ν)` and `𝒮'(χ) = {ν ∈ 𝒮₄(C) | (χ, δ_ν) ≠ 0}`.

The paper's proof is "`ν ∈ 𝒮'(χ)` iff `𝒮(χ)` contains `ν` or `λ₂ν` (it cannot contain
both); then see Lemmas 2.4, 3.3, 3.4".  In this workspace `𝒮(χ) = bset C f χ` is defined
from a *coherent map* `f` (BG Theorem 2.3), so the proof has two halves:

* **an explicit coherent map in the `|S| = 4` case** (`l41_orbitCoherence_of_n_eq_two`):
  here `Λ = {1, λ₂}` (`L41Aux`), so the key `Λν ∪ (Λν)^s` of a character `ν ∈ Irr(H₀)` has
  two or four elements and consists of the two `Λ`-orbits `Λν` and `Λ ν^s`.  In each orbit
  the coherent extension is obtained from the case-`n = 2` splitting
  (`Work.BG.TwoCaseProp`) of `δ_ν = (ν - λ₂ν)*`, whose norm is `4` when `ν^s = ν` and `2`
  otherwise (`l41_delta_inner_self`); the value clause (vi) of coherence is clause (vi) of
  BG Theorem 2.3, i.e. `Work.BG.ViProp` (`Work.BG.l41Vi`).  The per-key maps are pasted into
  one global map by the (proved) assemblies `s02_assemblyCore`/`s02_assemblyFull`.
* **the derivation of Lemma 4.1 from Lemmas 2.4, 3.3, 3.4** (`l41_main`), which uses
  `Work.BG.l41Shape` for the shape of `𝒮(χ)`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

section Helpers

variable (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]

/-- `ind C (ν - ν) = 0`. -/
@[simp] theorem l41_ind_self_sub (ν : ClassFunction ↥C.P.H0 ℂ) : ind C (ν - ν) = 0 := by
  rw [sub_self]
  exact ClassFunction.induce_zero C.P.H0

/-- The two-element set as a set-builder. -/
theorem l41_pair_eq (a b : ClassFunction ↥C.P.H0 ℂ) :
    {x : ClassFunction ↥C.P.H0 ℂ | x = a ∨ x = b} = ({a, b} : Set _) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]

end Helpers

section Symm

variable [Invertible (Nat.card G : ℂ)]

/-- `DisjointCF` is symmetric. -/
theorem l41_disjointCF_symm {α β : ClassFunction G ℂ} (h : DisjointCF α β) :
    DisjointCF β α := fun χ => (h χ).elim Or.inr Or.inl

end Symm

section Coherence

variable (D : Work.GW2.BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]

/-- **The per-orbit coherence of BG Theorem 2.3 in the `|S| = 4` case, `s`-fixed `ν`.**

Here `Λν = {ν, λ₂ν}` and both members are `s`-fixed, so the key is `{ν, λ₂ν}`.  Lemma 1.3
gives `δ_ν = (ν - λ₂ν)* ∈ ℤ[Irr G]` of degree `0` and norm `4`, so the case-`n = 2`
splitting (`Work.BG.TwoCaseProp` with `a = 2`) writes `δ_ν = g₁ - g₂` with `g₁, g₂` disjoint
of norm `2`; the good map is `ν ↦ g₁`, `λ₂ν ↦ g₂`.  Clause (vi) is vacuous (`ν` and `λ₂ν`
are `s`-fixed). -/
theorem l41_goodOn_fixed (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2)
    {β₂ : quotGroup C.P →* ℂˣ} (hβ : β₂ ≠ 1)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) (hfix : sconj C ν = ν) :
    ∃ f, GoodOn C (orbitKey C ν) f := by
  classical
  have h2 : Nat.card (quotGroup C.P) = 2 := quotGroup_card_two D C hc hn
  have hδZ : Work.GW2.C16.delta C β₂ ν ∈ ZIrr G := l41_delta_mem_ZIrr (β₂ := β₂) C hν
  have hδ1 : Work.GW2.C16.delta C β₂ ν 1 = 0 := l41_delta_apply_one (β₂ := β₂) C hν
  have hδn : ClassFunction.inner (Work.GW2.C16.delta C β₂ ν) (Work.GW2.C16.delta C β₂ ν)
      = 2 * (2 : ℂ) := by
    rw [l41_delta_inner_self C h2 hβ hν, if_pos hfix]
    norm_num
  obtain ⟨g₁, g₂, hg1, hg2, hn1, hn2, hsub, hdisj⟩ :=
    s02_twoCase (Work.GW2.C16.delta C β₂ ν) 2 (Or.inr rfl) hδZ hδ1 hδn
  have hlam_fix : sconj C (lamCF C β₂ * ν) = lamCF C β₂ * ν :=
    (sconj_lam_two_mul_eq_iff C h2 hβ ν).mpr hfix
  have hne : lamCF C β₂ * ν ≠ ν := lam_two_mul_ne_self C h2 hβ hν
  let f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ := fun μ =>
    if μ = ν then g₁ else if μ = lamCF C β₂ * ν then g₂ else 0
  have hf_ν : f ν = g₁ := by simp [f]
  have hf_lam : f (lamCF C β₂ * ν) = g₂ := by simp [f, hne]
  have hE : orbitKey C ν = ({ν, lamCF C β₂ * ν} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    rw [orbitKey_eq C h2 hβ ν, hfix, Set.union_self, l41_pair_eq]
  have hsub' : ind C (ν - lamCF C β₂ * ν) = f ν - f (lamCF C β₂ * ν) := by
    rw [hf_ν, hf_lam]
    exact hsub
  have hsub'' : ind C (lamCF C β₂ * ν - ν) = f (lamCF C β₂ * ν) - f ν := by
    rw [l41_ind_neg_sub C (lamCF C β₂ * ν) ν, hsub']
    abel
  refine ⟨f, ?_⟩
  intro μ hμ ν' hν' hμirr hν'irr
  rw [hE] at hμ hν'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hμ hν'
  rcases hν' with hν' | hν'
  · -- `ν' = ν`: both `ν` and `λ₂ν` are `s`-fixed, so clause (vi) is vacuous
    rw [hν']
    rcases hμ with hμ | hμ
    · -- `μ = ν`
      rw [hμ]
      refine ⟨?_, ?_, ?_, ?_, ?_, fun hc' => absurd hfix hc'⟩
      · rw [hf_ν]; exact hg1
      · rw [hf_ν, hfix, hf_ν]
      · rw [hf_ν, if_pos hfix]; exact hn1
      · intro _
        rw [hf_ν, l41_ind_self_sub C, sub_self]
      · intro _ h1 _
        exact absurd rfl h1
    · -- `μ = λ₂ν`
      rw [hμ]
      refine ⟨?_, ?_, ?_, ?_, ?_, fun hc' => absurd hfix hc'⟩
      · rw [hf_ν]; exact hg1
      · rw [hf_ν, hfix, hf_ν]
      · rw [hf_ν, if_pos hfix]; exact hn1
      · intro _
        exact hsub''
      · intro _ _ _
        rw [hf_ν, hf_lam]
        exact l41_disjointCF_symm hdisj
  · -- `ν' = λ₂ν`
    rw [hν']
    rcases hμ with hμ | hμ
    · -- `μ = ν`
      rw [hμ]
      refine ⟨?_, ?_, ?_, ?_, ?_, fun hc' => absurd hlam_fix hc'⟩
      · rw [hf_lam]; exact hg2
      · rw [hf_lam, hlam_fix, hf_lam]
      · rw [hf_lam, if_pos hlam_fix]; exact hn2
      · intro _
        exact hsub'
      · intro _ _ _
        rw [hf_ν, hf_lam]
        exact hdisj
    · -- `μ = λ₂ν`
      rw [hμ]
      refine ⟨?_, ?_, ?_, ?_, ?_, fun hc' => absurd hlam_fix hc'⟩
      · rw [hf_lam]; exact hg2
      · rw [hf_lam, hlam_fix, hf_lam]
      · rw [hf_lam, if_pos hlam_fix]; exact hn2
      · intro _
        rw [hf_lam, l41_ind_self_sub C, sub_self]
      · intro _ h1 _
        exact absurd rfl h1

/-- **The per-orbit coherence of BG Theorem 2.3 in the `|S| = 4` case, non-`s`-fixed `ν`.**

Now `ν^s ∉ Λν` (`sconj_ne_lam_two_mul`), so the key is the four-element set
`Λν ∪ Λ ν^s = {ν, λ₂ν, ν^s, λ₂ν^s}`.  `δ_ν = (ν - λ₂ν)*` has norm `2`, so the case-`n = 2`
splitting (`Work.BG.TwoCaseProp` with `a = 1`) writes `δ_ν = g₁ - g₂` with `g₁, g₂` disjoint
of norm `1`, and `δ_{ν^s} = (ν^s - λ₂ν^s)* = (ν - λ₂ν)*` (induction does not see `s`);
the good map is `ν, ν^s ↦ g₁` and `λ₂ν, λ₂ν^s ↦ g₂`, which makes `f ∘ sconj = f`.  Clause
(vi) is BG 2.3(vi), i.e. `Work.BG.ViProp` (`Work.BG.l41Vi`). -/
theorem l41_goodOn_moved (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2)
    {β₂ : quotGroup C.P →* ℂˣ} (hβ : β₂ ≠ 1)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) (hmov : sconj C ν ≠ ν) :
    ∃ f, GoodOn C (orbitKey C ν) f := by
  classical
  have h2 : Nat.card (quotGroup C.P) = 2 := quotGroup_card_two D C hc hn
  have hδZ : Work.GW2.C16.delta C β₂ ν ∈ ZIrr G := l41_delta_mem_ZIrr (β₂ := β₂) C hν
  have hδ1 : Work.GW2.C16.delta C β₂ ν 1 = 0 := l41_delta_apply_one (β₂ := β₂) C hν
  have hδn : ClassFunction.inner (Work.GW2.C16.delta C β₂ ν) (Work.GW2.C16.delta C β₂ ν)
      = 2 * ((1 : ℕ) : ℂ) := by
    rw [l41_delta_inner_self C h2 hβ hν, if_neg hmov]
    norm_num
  obtain ⟨g₁, g₂, hg1, hg2, hn1, hn2, hsub, hdisj⟩ :=
    s02_twoCase (Work.GW2.C16.delta C β₂ ν) 1 (Or.inl rfl) hδZ hδ1 hδn
  have hpm1 : IsPmIrr g₁ := isPmIrr_of_mem_ZIrr_inner_self_eq_one hg1 (by simpa using hn1)
  have hpm2 : IsPmIrr g₂ := isPmIrr_of_mem_ZIrr_inner_self_eq_one hg2 (by simpa using hn2)
  -- irreducibility and `s`-motion of the four key elements
  have hlam_irr : IsIrreducibleCharacter (lamCF C β₂ * ν) := lam_two_mul_irr C hν
  have hs_irr : IsIrreducibleCharacter (sconj C ν) := IsIrreducibleCharacter.conjByH C.P C.s hν
  have hlam_mov : sconj C (lamCF C β₂ * ν) ≠ lamCF C β₂ * ν :=
    fun h => hmov ((sconj_lam_two_mul_eq_iff C h2 hβ ν).mp h)
  have hs_mov : sconj C (sconj C ν) ≠ sconj C ν := by
    rw [sconj_sconj C ν]
    exact fun h => hmov h.symm
  have hlam_s_mov : sconj C (lamCF C β₂ * sconj C ν) ≠ lamCF C β₂ * sconj C ν :=
    fun h => hs_mov ((sconj_lam_two_mul_eq_iff C h2 hβ (sconj C ν)).mp h)
  -- distinctness of the four elements
  have hne_lam : lamCF C β₂ * ν ≠ ν := lam_two_mul_ne_self C h2 hβ hν
  have hne_slam : lamCF C β₂ * sconj C ν ≠ sconj C ν :=
    lam_two_mul_ne_self C h2 hβ hs_irr
  have hne_lam_slam : lamCF C β₂ * ν ≠ lamCF C β₂ * sconj C ν := by
    intro h
    refine hmov ?_
    have hh := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => lamCF C β₂ * φ) h
    rw [← mul_assoc_cf, ← mul_assoc_cf, lamCF_two_mul_self C h2, one_mul_cf,
      one_mul_cf] at hh
    exact hh.symm
  have hne_lams : lamCF C β₂ * sconj C ν ≠ ν := by
    intro h
    refine sconj_ne_lam_two_mul C h2 hβ hν ?_
    have hh := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => lamCF C β₂ * φ) h
    rw [← mul_assoc_cf, lamCF_two_mul_self C h2, one_mul_cf] at hh
    exact hh
  -- the map and its values on the key
  let f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ := fun μ =>
    if μ = ν then g₁
    else if μ = lamCF C β₂ * ν then g₂
    else if μ = sconj C ν then g₁
    else if μ = lamCF C β₂ * sconj C ν then g₂ else 0
  have hf_ν : f ν = g₁ := by simp [f]
  have hf_lam : f (lamCF C β₂ * ν) = g₂ := by simp [f, hne_lam]
  have hf_s : f (sconj C ν) = g₁ := by
    simp only [f]
    rw [if_neg hmov, if_neg (sconj_ne_lam_two_mul C h2 hβ hν)]
    simp
  have hf_slam : f (lamCF C β₂ * sconj C ν) = g₂ := by
    simp only [f]
    rw [if_neg hne_lams, if_neg (Ne.symm hne_lam_slam), if_neg hne_slam]
    simp
  have hE : orbitKey C ν = ({ν, lamCF C β₂ * ν} ∪ {sconj C ν, lamCF C β₂ * sconj C ν} :
      Set (ClassFunction ↥C.P.H0 ℂ)) := by
    rw [orbitKey_eq C h2 hβ ν, l41_pair_eq, l41_pair_eq]
  -- the induced characters of the two `Λ`-orbits
  have hsub' : ind C (ν - lamCF C β₂ * ν) = f ν - f (lamCF C β₂ * ν) := by
    rw [hf_ν, hf_lam]
    exact hsub
  have hsub'' : ind C (lamCF C β₂ * ν - ν) = f (lamCF C β₂ * ν) - f ν := by
    rw [l41_ind_neg_sub C (lamCF C β₂ * ν) ν, hsub']
    abel
  have hθs : ind C (sconj C ν - lamCF C β₂ * sconj C ν) = ind C (ν - lamCF C β₂ * ν) := by
    have h1 := l41_ind_sconj_sub C ν (lamCF C β₂ * ν)
    rwa [sconj_lam_two_mul C h2 hβ] at h1
  have hsubs : ind C (sconj C ν - lamCF C β₂ * sconj C ν)
      = f (sconj C ν) - f (lamCF C β₂ * sconj C ν) := by
    rw [hθs, hsub', hf_ν, hf_lam, hf_s, hf_slam]
  have hsubs' : ind C (lamCF C β₂ * sconj C ν - sconj C ν)
      = f (lamCF C β₂ * sconj C ν) - f (sconj C ν) := by
    rw [l41_ind_neg_sub C (lamCF C β₂ * sconj C ν) (sconj C ν), hsubs]
    abel
  -- the value clause (vi) at the four elements (BG 2.3(vi) = `ViProp`)
  have hVi₁ : g₁ (C.t : G) = 2 * ν C.t :=
    l41Vi C (lamCF C β₂ * ν) ν hlam_irr hν
      ⟨β₂, by rw [← mul_assoc_cf, lamCF_two_mul_self C h2, one_mul_cf]⟩ hlam_mov hmov
      (lam_two_mul_apply_t C h2 hβ ν) g₂ g₁ hpm2 hpm1
      (show ind C (lamCF C β₂ * ν - ν) = g₂ - g₁ by rw [hsub'', hf_lam, hf_ν])
  have hVi₂ : g₂ (C.t : G) = 2 * (lamCF C β₂ * ν) C.t :=
    l41Vi C ν (lamCF C β₂ * ν) hν hlam_irr ⟨β₂, rfl⟩ hmov hlam_mov
      (by rw [lam_two_mul_apply_t C h2 hβ ν]; ring) g₁ g₂ hpm1 hpm2
      (show ind C (ν - lamCF C β₂ * ν) = g₁ - g₂ by rw [hsub', hf_ν, hf_lam])
  -- the four "value packages" (everything except clauses (iii) and (iv))
  have keyν : f ν ∈ ZIrr G ∧ f (sconj C ν) = f ν ∧
      ClassFunction.inner (f ν) (f ν) = (if sconj C ν = ν then 2 else 1) ∧
      f ν (C.t : G) = 2 * ν C.t :=
    ⟨by rw [hf_ν]; exact hg1, by rw [hf_s, hf_ν],
      by rw [hf_ν, if_neg hmov]; simpa using hn1,
      by rw [hf_ν]; exact hVi₁⟩
  have keys : f (sconj C ν) ∈ ZIrr G ∧ f (sconj C (sconj C ν)) = f (sconj C ν) ∧
      ClassFunction.inner (f (sconj C ν)) (f (sconj C ν))
        = (if sconj C (sconj C ν) = sconj C ν then 2 else 1) ∧
      f (sconj C ν) (C.t : G) = 2 * (sconj C ν) C.t :=
    ⟨by rw [hf_s]; exact hg1,
      by rw [sconj_sconj C ν, hf_ν, hf_s],
      by rw [hf_s, if_neg hs_mov]; simpa using hn1,
      by rw [hf_s, sconj_apply_t C ν]; exact hVi₁⟩
  have keyf : f (lamCF C β₂ * ν) ∈ ZIrr G ∧
      f (sconj C (lamCF C β₂ * ν)) = f (lamCF C β₂ * ν) ∧
      ClassFunction.inner (f (lamCF C β₂ * ν)) (f (lamCF C β₂ * ν))
        = (if sconj C (lamCF C β₂ * ν) = lamCF C β₂ * ν then 2 else 1) ∧
      f (lamCF C β₂ * ν) (C.t : G) = 2 * (lamCF C β₂ * ν) C.t :=
    ⟨by rw [hf_lam]; exact hg2,
      by rw [sconj_lam_two_mul C h2 hβ ν, hf_slam, hf_lam],
      by rw [hf_lam, if_neg hlam_mov]; simpa using hn2,
      by rw [hf_lam]; exact hVi₂⟩
  have keyfs : f (lamCF C β₂ * sconj C ν) ∈ ZIrr G ∧
      f (sconj C (lamCF C β₂ * sconj C ν)) = f (lamCF C β₂ * sconj C ν) ∧
      ClassFunction.inner (f (lamCF C β₂ * sconj C ν)) (f (lamCF C β₂ * sconj C ν))
        = (if sconj C (lamCF C β₂ * sconj C ν) = lamCF C β₂ * sconj C ν then 2 else 1) ∧
      f (lamCF C β₂ * sconj C ν) (C.t : G) = 2 * (lamCF C β₂ * sconj C ν) C.t :=
    ⟨by rw [hf_slam]; exact hg2,
      by rw [sconj_lam_two_mul C h2 hβ (sconj C ν), sconj_sconj C ν, hf_lam, hf_slam],
      by rw [hf_slam, if_neg hlam_s_mov]; simpa using hn2,
      by rw [hf_slam, lam_two_mul_apply_t C h2 hβ (sconj C ν), sconj_apply_t C ν,
        ← lam_two_mul_apply_t C h2 hβ ν]
         exact hVi₂⟩
  -- `μ` is determined up to `λ₂` by `LamEquiv C μ ν'`
  have hmu_of {μ ν' : ClassFunction ↥C.P.H0 ℂ} (hLam : LamEquiv C μ ν') :
      ν' = μ ∨ ν' = lamCF C β₂ * μ := (LamEquiv_iff C h2 hβ μ ν').mp hLam
  have hmu_cancel (μ : ClassFunction ↥C.P.H0 ℂ) :
      lamCF C β₂ * (lamCF C β₂ * μ) = μ := by
    rw [← mul_assoc_cf, lamCF_two_mul_self C h2, one_mul_cf]
  have hmu_cancel_eq {μ μ' : ClassFunction ↥C.P.H0 ℂ}
      (h : lamCF C β₂ * μ = lamCF C β₂ * μ') : μ = μ' := by
    rw [← hmu_cancel μ, ← hmu_cancel μ', h]
  refine ⟨f, ?_⟩
  intro μ hμ ν' hν' hμirr hν'irr
  rw [hE] at hμ hν'
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hμ hν'
  rcases hν' with (hν' | hν') | (hν' | hν')
  · -- `ν' = ν`
    rw [hν']
    refine ⟨keyν.1, keyν.2.1, keyν.2.2.1, ?_, ?_, fun _ _ => keyν.2.2.2⟩
    · intro hLam
      rcases hmu_of hLam with h | h
      · rw [← h]; simp
      · have : μ = lamCF C β₂ * ν := by rw [← hmu_cancel μ, h]
        rw [this]
        exact hsub''
    · intro hLam h1 _
      rcases hmu_of hLam with h | h
      · rw [← h] at h1
        exact absurd rfl h1
      · have : μ = lamCF C β₂ * ν := by rw [← hmu_cancel μ, h]
        rw [this, hf_lam, hf_ν]
        exact l41_disjointCF_symm hdisj
  · -- `ν' = λ₂ν`
    rw [hν']
    refine ⟨keyf.1, keyf.2.1, keyf.2.2.1, ?_, ?_, fun _ _ => keyf.2.2.2⟩
    · intro hLam
      rcases hmu_of hLam with h | h
      · rw [← h]; simp
      · have : μ = ν := hmu_cancel_eq h.symm
        rw [this]
        exact hsub'
    · intro hLam h1 _
      rcases hmu_of hLam with h | h
      · rw [← h] at h1
        exact absurd rfl h1
      · have : μ = ν := hmu_cancel_eq h.symm
        rw [this, hf_ν, hf_lam]
        exact hdisj
  · -- `ν' = ν^s`
    rw [hν']
    refine ⟨keys.1, keys.2.1, keys.2.2.1, ?_, ?_, fun _ _ => keys.2.2.2⟩
    · intro hLam
      rcases hmu_of hLam with h | h
      · rw [← h]; simp
      · have : μ = lamCF C β₂ * sconj C ν := by rw [← hmu_cancel μ, h]
        rw [this]
        exact hsubs'
    · intro hLam h1 _
      rcases hmu_of hLam with h | h
      · rw [← h] at h1
        exact absurd rfl h1
      · have : μ = lamCF C β₂ * sconj C ν := by rw [← hmu_cancel μ, h]
        rw [this, hf_slam, hf_s]
        exact l41_disjointCF_symm hdisj
  · -- `ν' = λ₂ν^s`
    rw [hν']
    refine ⟨keyfs.1, keyfs.2.1, keyfs.2.2.1, ?_, ?_, fun _ _ => keyfs.2.2.2⟩
    · intro hLam
      rcases hmu_of hLam with h | h
      · rw [← h]; simp
      · have : μ = sconj C ν := hmu_cancel_eq h.symm
        rw [this]
        exact hsubs
    · intro hLam h1 _
      rcases hmu_of hLam with h | h
      · rw [← h] at h1
        exact absurd rfl h1
      · have : μ = sconj C ν := hmu_cancel_eq h.symm
        rw [this, hf_s, hf_slam]
        exact hdisj

end Coherence

section Assembly

variable (D : Work.GW2.BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]

/-- **The per-orbit coherence of BG Theorem 2.3 in the `|S| = 4` case.** -/
theorem l41_orbitCoherence_of_n_eq_two (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2)
    {β₂ : quotGroup C.P →* ℂˣ} (hβ : β₂ ≠ 1) : OrbitCoherenceProp C := by
  intro ν hν
  by_cases hfix : sconj C ν = ν
  · exact l41_goodOn_fixed D C hc hn hβ hν hfix
  · exact l41_goodOn_moved D C hc hn hβ hν hfix

/-- **BG Theorem 2.3 in the `|S| = 4` case**: `C` has a coherent map. -/
theorem l41_isCoherent_exists (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2)
    {β₂ : quotGroup C.P →* ℂˣ} (hβ : β₂ ≠ 1) : ∃ f, Work.GW2.C16.IsCoherent C f := by
  have hOC : OrbitCoherenceProp C := l41_orbitCoherence_of_n_eq_two D C hc hn hβ
  have hcore : Coherence23CoreProp C := s02_assemblyCore C (sconjLam C) hOC
  have hcoh : Coherence23Prop C :=
    s02_assemblyFull C (s02_gram C) (s02_bsValueT C) hcore
  exact (Work.GW2.C16.coherence23_iff C).mp hcoh

end Assembly

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem lemma41 {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Work.GW2.C16.Lemma41Prop D C := by
  intro hc hn β₂ hβ χ hχ hne
  obtain ⟨f, hf⟩ := l41_isCoherent_exists D C hc hn hβ
  obtain ⟨hs1, hs2, hs3, hs4⟩ := l41Shape D C hc hn β₂ hβ f hf χ hχ hne
  exact l41Deriv D C hc hn β₂ hβ f hf χ hχ hs2 hs3 hs4 hs1

end Work.BG
