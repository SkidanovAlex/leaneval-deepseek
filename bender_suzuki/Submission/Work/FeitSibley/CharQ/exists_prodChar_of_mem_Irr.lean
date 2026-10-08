import Mathlib
import Submission.Work.CharCore.sum_irr_degree_sq
import Submission.Work.FeitSibley.GroupTheory.S_Q1
import Submission.Work.FeitSibley.CharQ.prodChar_mem_Irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.CharQ.exists_prodChar_of_mem_Irr`

Every irreducible character of `Q = S × Q₁` is the tensor product `prodChar h lam theta` of an
irreducible character `lam` of `S` and an irreducible character `theta` of `Q₁`.

The proof is a degree count.  The map `(lam, theta) ↦ prodChar h lam theta` sends
`Irr S × Irr Q₁` injectively into `Irr Q` (`prodChar_mem_Irr`, `prodChar_inj`), so it suffices
to observe that the two sides carry the same total sum of squares of degrees.  By the sum of
squares formula `∑_{χ ∈ Irr G} χ(1)² = |G|` and multiplicativity of degrees
(`prodChar h lam theta 1 = lam 1 · theta 1`),

`∑_{Irr S × Irr Q₁} (deg ∘ prodChar)² = (∑_{Irr S} deg²)(∑_{Irr Q₁} deg²)
 = |S| · |Q₁| = |Q| = ∑_{Irr Q} deg²`,

and since every term is a positive integer an injection with equal total sum must exhaust its
codomain.
-/

noncomputable section

open Classical Finset

namespace Work.FeitSibley.CharQ

/-- The sum of squares of the degrees of the irreducible complex characters of a finite group,
stated in `ℕ`. -/
private lemma sum_irrDeg_sq {G : Type*} [Group G] [Fintype G] :
    ∑ χ ∈ Work.CharCore.Irr G, (Work.CharCore.irrDeg χ) ^ 2 = Nat.card G := by
  have h := Work.CharCore.sum_irr_degree_sq (G := G)
  apply Nat.cast_injective (R := ℂ)
  rw [Nat.cast_sum, ← h]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  rw [Nat.cast_pow, Work.CharCore.irrDeg_spec hχ]

/-- The same sum, indexed by the subtype `↥(Irr G)`. -/
private lemma sum_irrDeg_sq_univ {G : Type*} [Group G] [Fintype G] :
    ∑ χ : ↥(Work.CharCore.Irr G), (Work.CharCore.irrDeg χ.1) ^ 2 = Nat.card G := by
  have key : (∑ χ : ↥(Work.CharCore.Irr G), (Work.CharCore.irrDeg χ.1) ^ 2)
      = ∑ χ ∈ Work.CharCore.Irr G, (Work.CharCore.irrDeg χ) ^ 2 := by
    simpa using (Finset.sum_coe_sort (Work.CharCore.Irr G)
      (fun χ : G → ℂ => (Work.CharCore.irrDeg χ) ^ 2))
  rw [key, sum_irrDeg_sq]

/-- **Fibre counting.**  If `f : α → β` is injective between finite types and a positive
integer valued function `g` on `β` has the same total sum over `α` (via `f`) as over `β`, then
`f` is surjective.  Indeed `∑_β g = ∑_{f(α)} g + ∑_{β \ f(α)} g`, and the first summand is
`∑_α g ∘ f = ∑_β g`, so the second vanishes; as `g` is positive, `β \ f(α)` is empty. -/
private lemma surjective_of_injective_of_sum_eq {α β : Type*} [Fintype α] [Fintype β]
    {f : α → β} (hf : Function.Injective f) {g : β → ℕ} (hg : ∀ b, 0 < g b)
    (hsum : ∑ a, g (f a) = ∑ b, g b) : Function.Surjective f := by
  classical
  set s : Finset β := Finset.univ.image f with hs
  have hsimg : ∑ b ∈ s, g b = ∑ a, g (f a) := by
    rw [hs, Finset.sum_image]
    intro x _ y _ hxy
    exact hf hxy
  have hsplit : ∑ b ∈ Finset.univ \ s, g b + ∑ b ∈ s, g b = ∑ b, g b :=
    Finset.sum_sdiff (Finset.subset_univ s)
  rw [hsimg, hsum] at hsplit
  have hzero : ∑ b ∈ Finset.univ \ s, g b = 0 := by
    have := hsplit
    omega
  have hsempty : Finset.univ \ s = ∅ := by
    by_contra hne
    have hpos : 0 < ∑ b ∈ Finset.univ \ s, g b :=
      Finset.sum_pos (fun b _ => hg b) (Finset.nonempty_iff_ne_empty.mpr hne)
    omega
  have hsuniv : s = Finset.univ := by
    have hsub : Finset.univ ⊆ s := Finset.sdiff_eq_empty_iff_subset.mp hsempty
    exact Finset.eq_univ_iff_forall.mpr fun b => hsub (Finset.mem_univ b)
  intro b
  have hb : b ∈ s := hsuniv ▸ Finset.mem_univ b
  rw [hs, Finset.mem_image] at hb
  obtain ⟨a, _, ha⟩ := hb
  exact ⟨a, ha⟩

/-- **Injectivity of `prodChar`.**  If `lam, lam' ∈ Irr S` and `theta, theta' ∈ Irr Q₁` give
the same character of `Q = S × Q₁`, then they are equal.

Evaluating the identity on the factors `S × 1` and `1 × Q₁` shows `lam = d₁ • lam'` and
`theta = d₀ • theta'` for the nonzero scalars `d₁ = theta' 1 / theta 1` and
`d₀ = lam' 1 / lam 1`.  Orthonormality of `Irr` then forces `d₁, d₀ ∈ {0,1}`, and they are
nonzero, so `d₁ = d₀ = 1`. -/
private lemma prodChar_inj_aux {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {lam lam' : ↥h.S → ℂ} {theta theta' : ↥h.Q1 → ℂ}
    (hl : lam ∈ Work.CharCore.Irr ↥h.S) (hl' : lam' ∈ Work.CharCore.Irr ↥h.S)
    (ht : theta ∈ Work.CharCore.Irr ↥h.Q1) (ht' : theta' ∈ Work.CharCore.Irr ↥h.Q1)
    (heq : h.prodChar lam theta = h.prodChar lam' theta') : lam = lam' ∧ theta = theta' := by
  have hlam1 : lam 1 ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec hl]
    simp only [ne_eq, Nat.cast_eq_zero]
    exact (Work.CharCore.irrDeg_pos hl).ne'
  have hlam1' : lam' 1 ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec hl']
    simp only [ne_eq, Nat.cast_eq_zero]
    exact (Work.CharCore.irrDeg_pos hl').ne'
  have htheta1 : theta 1 ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec ht]
    simp only [ne_eq, Nat.cast_eq_zero]
    exact (Work.CharCore.irrDeg_pos ht).ne'
  have htheta1' : theta' 1 ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec ht']
    simp only [ne_eq, Nat.cast_eq_zero]
    exact (Work.CharCore.irrDeg_pos ht').ne'
  have hb1 : ∀ a : ↥h.S, lam a * theta 1 = lam' a * theta' 1 := by
    intro a
    have hh := congrFun heq (h.prodIso (a, (1 : ↥h.Q1)))
    simpa only [h.prodChar_apply] using hh
  have ha1 : ∀ b : ↥h.Q1, lam 1 * theta b = lam' 1 * theta' b := by
    intro b
    have hh := congrFun heq (h.prodIso ((1 : ↥h.S), b))
    simpa only [h.prodChar_apply] using hh
  set d1 : ℂ := theta' 1 / theta 1 with hd1def
  set d0 : ℂ := lam' 1 / lam 1 with hd0def
  have hd1ne : d1 ≠ 0 := by
    rw [hd1def]; exact div_ne_zero htheta1' htheta1
  have hd0ne : d0 ≠ 0 := by
    rw [hd0def]; exact div_ne_zero hlam1' hlam1
  have hd1mul : d1 * theta 1 = theta' 1 := by
    rw [hd1def, div_mul_cancel₀ _ htheta1]
  have hd0mul : d0 * lam 1 = lam' 1 := by
    rw [hd0def, div_mul_cancel₀ _ hlam1]
  have hlam_eq : lam = d1 • lam' := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul]
    refine mul_right_cancel₀ htheta1 ?_
    calc lam a * theta 1 = lam' a * theta' 1 := hb1 a
      _ = lam' a * (d1 * theta 1) := by rw [hd1mul]
      _ = (d1 * lam' a) * theta 1 := by ring
  have htheta_eq : theta = d0 • theta' := by
    funext b
    simp only [Pi.smul_apply, smul_eq_mul]
    refine mul_right_cancel₀ hlam1 ?_
    calc theta b * lam 1 = lam' 1 * theta' b := by rw [mul_comm (theta b) (lam 1), ha1 b]
      _ = (d0 * lam 1) * theta' b := by rw [hd0mul]
      _ = (d0 * theta' b) * lam 1 := by ring
  have hd1eq : d1 = (if lam = lam' then 1 else 0) := by
    have h1 : Work.CharCore.cfInner lam lam' = d1 := by
      rw [hlam_eq, Work.CharCore.cfInner_smul_left,
        Work.CharCore.irr_orthonormal lam' lam' hl' hl']
      simp
    rw [← h1, Work.CharCore.irr_orthonormal lam lam' hl hl']
  have hll : lam = lam' := by
    by_contra hne
    rw [ite_eq_right hne] at hd1eq
    exact hd1ne hd1eq
  have htt : theta = theta' := by
    by_contra hne
    have hd0eq : d0 = (if theta = theta' then 1 else 0) := by
      have h1 : Work.CharCore.cfInner theta theta' = d0 := by
        rw [htheta_eq, Work.CharCore.cfInner_smul_left,
          Work.CharCore.irr_orthonormal theta' theta' ht' ht']
        simp
      rw [← h1, Work.CharCore.irr_orthonormal theta theta' ht ht']
    rw [ite_eq_right hne] at hd0eq
    exact hd0ne hd0eq
  exact ⟨hll, htt⟩

theorem exists_prodChar_of_mem_Irr {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {phi : ↥h.Q → ℂ} (hphi : phi ∈ Work.CharCore.Irr ↥h.Q) :
    ∃ lam ∈ Work.CharCore.Irr ↥h.S, ∃ theta ∈ Work.CharCore.Irr ↥h.Q1,
      phi = h.prodChar lam theta := by
  classical
  -- the injective map `Irr S × Irr Q₁ → Irr Q`, `(lam, theta) ↦ prodChar h lam theta`
  let F : ↥(Work.CharCore.Irr ↥h.S) × ↥(Work.CharCore.Irr ↥h.Q1) →
      ↥(Work.CharCore.Irr ↥h.Q) :=
    fun p => ⟨h.prodChar p.1.1 p.2.1, prodChar_mem_Irr h p.1.2 p.2.2⟩
  have hF : Function.Injective F := by
    intro p q hpq
    have hval : h.prodChar p.1.1 p.2.1 = h.prodChar q.1.1 q.2.1 := congrArg Subtype.val hpq
    obtain ⟨e1, e2⟩ := prodChar_inj_aux h p.1.2 q.1.2 p.2.2 q.2.2 hval
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
  -- multiplicativity of degrees
  have hdeg : ∀ p : ↥(Work.CharCore.Irr ↥h.S) × ↥(Work.CharCore.Irr ↥h.Q1),
      Work.CharCore.irrDeg (F p).1
        = Work.CharCore.irrDeg p.1.1 * Work.CharCore.irrDeg p.2.1 := by
    intro p
    apply Nat.cast_injective (R := ℂ)
    rw [Nat.cast_mul, ← Work.CharCore.irrDeg_spec (F p).2,
      ← Work.CharCore.irrDeg_spec p.1.2, ← Work.CharCore.irrDeg_spec p.2.2]
    exact h.prodChar_one p.1.1 p.2.1
  -- the sum of squares over the domain
  have hsumF : ∑ p : ↥(Work.CharCore.Irr ↥h.S) × ↥(Work.CharCore.Irr ↥h.Q1),
      (Work.CharCore.irrDeg (F p).1) ^ 2 = Nat.card ↥h.S * Nat.card ↥h.Q1 := by
    rw [Fintype.sum_prod_type]
    simp only [hdeg, mul_pow]
    rw [← Finset.sum_mul_sum, sum_irrDeg_sq_univ, sum_irrDeg_sq_univ]
  -- the sum of squares over the codomain
  have hsumC : ∑ χ : ↥(Work.CharCore.Irr ↥h.Q), (Work.CharCore.irrDeg χ.1) ^ 2
      = Nat.card ↥h.S * Nat.card ↥h.Q1 := by
    rw [sum_irrDeg_sq_univ, ← Nat.card_congr h.prodIso.toEquiv, Nat.card_prod]
  have hsum_eq : (∑ p : ↥(Work.CharCore.Irr ↥h.S) × ↥(Work.CharCore.Irr ↥h.Q1),
      (Work.CharCore.irrDeg (F p).1) ^ 2)
      = ∑ χ : ↥(Work.CharCore.Irr ↥h.Q), (Work.CharCore.irrDeg χ.1) ^ 2 := by
    rw [hsumF, hsumC]
  have hsurj : Function.Surjective F :=
    surjective_of_injective_of_sum_eq hF
      (g := fun χ : ↥(Work.CharCore.Irr ↥h.Q) => (Work.CharCore.irrDeg χ.1) ^ 2)
      (fun χ => pow_pos (Work.CharCore.irrDeg_pos χ.2) 2) hsum_eq
  obtain ⟨p, hp⟩ := hsurj ⟨phi, hphi⟩
  exact ⟨p.1.1, p.1.2, p.2.1, p.2.2, (congrArg Subtype.val hp).symm⟩

end Work.FeitSibley.CharQ
