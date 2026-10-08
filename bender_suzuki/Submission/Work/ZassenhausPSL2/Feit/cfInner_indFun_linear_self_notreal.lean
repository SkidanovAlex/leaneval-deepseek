import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ZassenhausPSL2.ZData.t_conj_eq_inv
import Submission.Work.CharCore.Defs
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.CFun
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.star_Irr
import Submission.Work.Induction.Defs
import Submission.Work.Induction.Basic
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.Induction.isClassFun_indFun
import Submission.Work.ThmG2.cfInner_indFun_self_twoDoubleCoset
import Submission.Work.ZassenhausPSL2.Feit.linear_of_trivial_on_Q
import Submission.Work.ZassenhausPSL2.Feit.sum_monoidHom_units_eq_zero

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausPSL2.Feit.cfInner_indFun_linear_self_notreal` (Feit's leaf F4'', the `lc = lc'` case)

In a split rank-one Zassenhaus configuration `H = Q ⋊ D` (`D = twoPoint H t = H ⊓ Hᵗ`,
`Q ⊴ H` an abelian `2`-subgroup) let `lc ∈ Irr H` be trivial on `Q` — equivalently
(`Work.ZassenhausPSL2.Feit.linear_of_trivial_on_Q`) `lc` is a *linear* character of `H`, i.e.
`lc x = (φ x : ℂ)` for a homomorphism `φ : H →* ℂˣ` — and suppose moreover that `lc` is **not**
real-valued (`hreal`).  Then

`⟨Ind_H^G lc, Ind_H^G lc⟩_G = 1`,

i.e. the induced character `lc^G` is irreducible.

## The mathematics

`G = H ⊔ H·t·Q` (`Work.ZassenhausPSL2.exists_unique_decomp`), so `H` has exactly two
`(H,H)`-double cosets (`Work.ThmG2.cfInner_indFun_self_twoDoubleCoset`, a Mackey computation):

`⟨ψ^G, ψ^G⟩_G = ⟨ψ, ψ⟩_H + |D|⁻¹ ∑_{d ∈ D} ψ d · conj (ψ (t d t))`,

`D = twoPoint H t`.  For `ψ = lc` linear with `lc ≠ conj lc` the correction term vanishes:
since `t` inverts `D` (`Work.ZassenhausPSL2.ZData.t_conj_eq_inv`, Burnside's lemma) and
`conj (χ y) = χ y⁻¹` for a character (`Work.CharCore.star_Irr`), the summand at `d` is
`lc d · star (lc d⁻¹) = (lc d)²`, so the correction term is `|D|⁻¹ ∑_{d∈D} (λ d)²` for the
linear character `λ = lc|_D` — and `∑_{k∈K} ψ k = 0` for every *non-trivial* homomorphism
`ψ : K →* ℂˣ` of a finite group (multiplying the sum by `ψ k₀ ≠ 1` permutes it).  Non-triviality
of `λ · λ` is exactly the hypothesis `hreal`: since `lc` is trivial on `Q` and `H = Q·D`,
`(λ d)² = 1` for all `d` would force `lc` to be real-valued.

## Note on `Fintype` instances

As in the sibling leaves of this directory, `Work.CharCore.Irr ↥H` carries the `Fintype ↥H`
instance of the caller, whereas the Mackey formula
`Work.ThmG2.cfInner_indFun_self_twoDoubleCoset` was stated with the instance synthesised from
`[Fintype G]`.  `cfInner_inst_indep` and `mem_Irr_of_fintype_lin` below bridge the two.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open Classical

namespace Work.ZassenhausPSL2.Feit

/-- `Work.CharCore.cfInner` is independent of the chosen `Fintype` instance: the two instances
give the same `Finset.univ` (by extensionality) and the same cardinality (`Fintype.card` at any
instance is `Nat.card`). -/
private theorem cfInner_inst_indep {X : Type} (i₁ i₂ : Fintype X) (f g : X → ℂ) :
    @Work.CharCore.cfInner X i₁ f g = @Work.CharCore.cfInner X i₂ f g := by
  have huniv : (@Finset.univ X i₁ : Finset X) = @Finset.univ X i₂ :=
    Finset.ext fun x => by simp
  have hcard : (@Fintype.card X i₁ : ℂ) = (@Fintype.card X i₂ : ℂ) := by
    rw [@Fintype.card_eq_nat_card X i₁, @Fintype.card_eq_nat_card X i₂]
  have hsum : (@Finset.univ X i₁).sum (fun x => f x * starRingEnd ℂ (g x))
      = (@Finset.univ X i₂).sum (fun x => f x * starRingEnd ℂ (g x)) := by
    rw [huniv]
  show (@Fintype.card X i₁ : ℂ)⁻¹ * (@Finset.univ X i₁).sum (fun x => f x * starRingEnd ℂ (g x))
      = (@Fintype.card X i₂ : ℂ)⁻¹ *
          (@Finset.univ X i₂).sum (fun x => f x * starRingEnd ℂ (g x))
  rw [hcard, hsum]

/-- Membership in `Work.CharCore.Irr` is independent of the chosen `Fintype` instance: both
`Finset`s consist of the characters of the simple finite dimensional complex representations
(`Work.CharCore.mem_Irr_iff_fdrep`). -/
private lemma mem_Irr_of_fintype_lin {X : Type} [Group X] {i₁ i₂ : Fintype X} {ψ : X → ℂ}
    (h : ψ ∈ @Work.CharCore.Irr X _ i₁) : ψ ∈ @Work.CharCore.Irr X _ i₂ := by
  rw [@Work.CharCore.mem_Irr_iff_fdrep X _ i₁ ψ] at h
  rw [@Work.CharCore.mem_Irr_iff_fdrep X _ i₂ ψ]
  exact h

/-- A complex number with `z * z = 1` is real. -/
private lemma star_eq_self_of_mul_self {z : ℂ} (hz : z * z = 1) : star z = z := by
  have h : (z - 1) * (z + 1) = 0 := by
    calc (z - 1) * (z + 1) = z * z - 1 := by ring
      _ = 0 := by rw [hz]; ring
  rcases mul_eq_zero.mp h with h1 | h1
  · have hz1 : z = 1 := sub_eq_zero.mp h1
    rw [hz1]; simp
  · have hz1 : z = -1 := by rw [add_eq_zero_iff_eq_neg] at h1; exact h1
    rw [hz1]; simp

theorem cfInner_indFun_linear_self_notreal {G : Type} [Group G] [Fintype G] {H Q : Subgroup G}
    [Fintype ↥H] {t : G} (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hz : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (hab : Submission.Blueprint.IsAbelianSubgroup Q) {lc : H → ℂ}
    (hlc : lc ∈ Work.CharCore.Irr H) (hlcQ : ∀ x : H, (x : G) ∈ Q → lc x = 1)
    (hreal : lc ≠ fun x => starRingEnd ℂ (lc x)) :
    Work.CharCore.cfInner (Work.Induction.indFun H lc) (Work.Induction.indFun H lc) = 1 := by
  -- ## Step 1: the two-double-coset (Mackey) formula
  have ht : t * t = 1 := Work.ZassenhausPSL2.t_mul_t h
  have hcover : ∀ g : G, g ∈ H ∨ ∃ a b : H, g = (a : G) * t * (b : G) := by
    intro g
    by_cases hg : g ∈ H
    · exact Or.inl hg
    · right
      obtain ⟨⟨a, q⟩, hspec, -⟩ := Work.ZassenhausPSL2.exists_unique_decomp h hg
      exact ⟨a, ⟨(q : G), h.le q.2⟩, by simpa using hspec.symm⟩
  have hDmap : ∀ d : ↥(H ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) H),
      (MulAut.conj t) (d : G) ∈ H ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) H := by
    intro d
    have h1 : MulAut.conj t (d : G) = t * (d : G) * t := by
      rw [MulAut.conj_apply, Work.ZassenhausPSL2.t_inv h]
    rw [h1]
    exact Work.ZassenhausPSL2.dStab_conj_mem h d.2
  have hmain := Work.ThmG2.cfInner_indFun_self_twoDoubleCoset (G := G) ht h.not_mem hcover hDmap lc
    (Work.CharCore.isClassFun_of_mem_Irr hlc)
  rw [hmain]
  -- ## Step 2: `⟨lc, lc⟩_H = 1`
  have horth : ∀ (i : Fintype ↥H), @Work.CharCore.cfInner ↥H i lc lc = 1 := by
    intro i
    have hlc_i : lc ∈ @Work.CharCore.Irr ↥H _ i := mem_Irr_of_fintype_lin hlc
    rw [@Work.CharCore.irr_orthonormal ↥H _ i lc lc hlc_i hlc_i]
    simp
  rw [horth]
  -- ## Step 3: `Q` is non-trivial, and `lc` is a linear character
  have hQ : Q ≠ ⊥ := by
    intro hbot
    have htwo : Submission.Blueprint.twoPoint H t = H := by
      have hs : Q ⊔ Submission.Blueprint.twoPoint H t = H := h.sup_eq
      rw [hbot, bot_sup_eq] at hs
      exact hs
    have hodd : Odd (Nat.card (Submission.Blueprint.twoPoint H t)) :=
      Work.ZassenhausPSL2.dStab_odd H t h.stronglyEmbedded h.not_mem
    rw [htwo] at hodd
    exact (Nat.not_odd_iff_even.mpr h.stronglyEmbedded.2.1) hodd
  have htinverts : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t → t * d * t = d⁻¹ :=
    Work.ZassenhausPSL2.ZData.t_conj_eq_inv H Q t h hz hQ h2
  obtain ⟨φ, hφ⟩ := Work.ZassenhausPSL2.Feit.linear_of_trivial_on_Q h hz h2 hab hlc hlcQ
  -- ## Step 4: the correction term vanishes
  have hsum : ∀ (i : Fintype ↥(Submission.Blueprint.twoPoint H t)),
      (@Finset.univ ↥(Submission.Blueprint.twoPoint H t) i).sum
        (fun d => lc ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ *
          star (lc ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩)) = 0 := by
    intro i
    let lam : ↥(Submission.Blueprint.twoPoint H t) →* ℂˣ :=
      φ.comp (Subgroup.inclusion (inf_le_left : Submission.Blueprint.twoPoint H t ≤ H))
    have hlam2 : lam * lam ≠ 1 := by
      intro hcon
      apply hreal
      funext x
      obtain ⟨d, q, hdq⟩ := Work.ZassenhausPSL2.mem_eq_dStab_mul_Q h x
      have hx : x = (Subgroup.inclusion (inf_le_left : Submission.Blueprint.twoPoint H t ≤ H) d) *
          (⟨(q : G), h.le q.2⟩ : ↥H) := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_inclusion]
        exact hdq.symm
      have hmul : ∀ a b : ↥H, lc (a * b) = lc a * lc b := by
        intro a b
        rw [hφ (a * b), map_mul, Units.val_mul, hφ a, hφ b]
      have hq1 : lc (⟨(q : G), h.le q.2⟩ : ↥H) = 1 := hlcQ _ (show (q : G) ∈ Q from q.2)
      have hdd : (lam d) * (lam d) = 1 := by
        have := congrArg (fun f : ↥(Submission.Blueprint.twoPoint H t) →* ℂˣ => f d) hcon
        simpa using this
      have hinc : lc (Subgroup.inclusion (inf_le_left : Submission.Blueprint.twoPoint H t ≤ H) d) *
          lc (Subgroup.inclusion (inf_le_left : Submission.Blueprint.twoPoint H t ≤ H) d) = 1 := by
        have h3 : lc (Subgroup.inclusion (inf_le_left : Submission.Blueprint.twoPoint H t ≤ H) d)
            = (lam d : ℂ) := hφ _
        rw [h3, ← Units.val_mul, hdd, Units.val_one]
      have hdx : lc x = lc (Subgroup.inclusion (inf_le_left : Submission.Blueprint.twoPoint H t ≤ H) d) := by
        calc lc x = lc ((Subgroup.inclusion
                (inf_le_left : Submission.Blueprint.twoPoint H t ≤ H) d) *
              (⟨(q : G), h.le q.2⟩ : ↥H)) := by rw [hx]
          _ = lc (Subgroup.inclusion (inf_le_left : Submission.Blueprint.twoPoint H t ≤ H) d) *
              lc (⟨(q : G), h.le q.2⟩ : ↥H) := hmul _ _
          _ = lc (Subgroup.inclusion (inf_le_left : Submission.Blueprint.twoPoint H t ≤ H) d) := by
                rw [hq1, mul_one]
      rw [hdx]
      exact (star_eq_self_of_mul_self hinc).symm
    have hpt : ∀ d : ↥(Submission.Blueprint.twoPoint H t),
        lc ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ *
          star (lc ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩)
        = ((lam * lam) d : ℂ) := by
      intro d
      have hconj : MulAut.conj t (d : G) = ((d : G))⁻¹ := by
        rw [MulAut.conj_apply, Work.ZassenhausPSL2.t_inv h]
        exact htinverts (d : G) d.2
      have hsubH : (⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩ : ↥H)
          = (Subgroup.inclusion (inf_le_left : Submission.Blueprint.twoPoint H t ≤ H) d)⁻¹ := by
        apply Subtype.ext
        rw [Subgroup.coe_inv, Subgroup.coe_inclusion]
        simpa using hconj
      have hstar : star (lc ((Subgroup.inclusion
          (inf_le_left : Submission.Blueprint.twoPoint H t ≤ H) d)⁻¹))
          = lc (Subgroup.inclusion (inf_le_left : Submission.Blueprint.twoPoint H t ≤ H) d) := by
        have h := Work.CharCore.star_Irr lc hlc
          ((Subgroup.inclusion (inf_le_left : Submission.Blueprint.twoPoint H t ≤ H) d)⁻¹)
        rw [inv_inv] at h
        simpa only [starRingEnd_apply] using h
      rw [hsubH, hstar]
      have h1' : lc ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ = (lam d : ℂ) := hφ _
      have h1'' : lc (Subgroup.inclusion (inf_le_left : Submission.Blueprint.twoPoint H t ≤ H) d)
          = (lam d : ℂ) := hφ _
      rw [h1', h1'']
      simp only [MonoidHom.mul_apply, Units.val_mul]
    rw [Finset.sum_congr rfl (fun d _ => hpt d)]
    exact sum_monoidHom_units_eq_zero (lam * lam) hlam2
  rw [hsum]
  ring

end Work.ZassenhausPSL2.Feit
