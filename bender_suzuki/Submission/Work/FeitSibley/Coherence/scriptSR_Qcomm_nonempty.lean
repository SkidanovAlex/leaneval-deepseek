import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.CharQ.scriptS_eq_image
import Submission.Work.FeitSibley.Coherence.H_le_normalizer_FSQcomm
import Submission.Work.CohApps.sum_irr_deg_sq_le_ker
import Submission.Work.CharCore.column_orthogonality_not_conj
import Submission.Work.CharCore.linear_char_iff_deg_one
import Submission.Work.CharCore.sum_irr_degree_sq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.scriptSR_Qcomm_nonempty`

Peterfalvi II, Appendice XII (p. 288): for the Feit–Sibley data `h : FSData G`, if `Q₁` has a
non-trivial **linear** character then the set

`𝒮(Q') = scriptSR h.H h.Q₁ Q'`,  `Q' = ⁅Q,Q⁆`,

of irreducible characters of `H` which are non-trivial on `Q₁` and trivial on the derived
subgroup of `Q`, is non-empty.

## The argument

The extra hypothesis on `Q₁` is exactly what makes `Q₁ ⊄ Q'` true, and therefore makes `𝒮(Q')`
non-empty:

* `𝒮(Q')` consists of the irreducible characters of `H` with `Q' ≤ ker χ` and `Q₁ ⊄ ker χ`;
* `Q' ≤ ker χ` means that `χ` is the inflation of an irreducible character `χ'` of the quotient
  `H/Q'` (here `Q'` is normal in `H` because `Q ⊴ H` and `Q' ` is characteristic in `Q`);
* `Q₁ ⊄ ker χ` means that `χ'` is non-trivial at the image of some element of `Q₁`.

Since `Q = S · Q₁` is the direct product of `S` and `Q₁` (`S_sup_Q1`, `S_inf_Q1`, `commute`),
one has `Q₁ ⊓ Q' = [Q₁,Q₁]`.  The hypothesis gives a non-trivial homomorphism `φ : Q₁ →* ℂˣ`,
which therefore is non-trivial at some `y ∈ Q₁ \ [Q₁,Q₁]`; extending `φ` to `Q` by `Φ(a·b) = φ b`
(a monoid homomorphism as `Q ≅ S × Q₁`), and using that a homomorphism into the abelian group
`ℂˣ` kills commutators, shows `y ∉ Q'`.

Let `ū ≠ 1` be the image of `y` in `K = H ⧸ Q'`.  The general fact that characters separate
points (`exists_irr_apply_ne_one`: for `1 ≠ z` in a finite group there is `χ ∈ Irr` with
`χ z ≠ χ 1` — the non-conjugate case of column orthogonality) supplies `χ' ∈ Irr K` with
`χ' ū ≠ χ' 1`; its inflation `χ = inflateFun Q' χ'` is irreducible, trivial on `Q'` and
non-trivial on `Q₁`, i.e. `χ ∈ 𝒮(Q')`.

## Contents

* `exists_irr_apply_ne_one` — characters separate points;
* `exists_mem_Q1_notMem_FSQcomm` — a non-trivial linear character of `Q₁` yields an element of
  `Q₁` outside `⁅Q,Q⁆` (only the proof uses this; it is `private`);
* `scriptSR_Qcomm_nonempty` — the requested statement.
-/

set_option linter.style.haveILetI false

namespace Work.FeitSibley.Coherence

open Classical

noncomputable section

/-- **Characters separate points.**  For `1 ≠ x` in a finite group there is an irreducible
complex character `χ` with `χ x ≠ χ 1`.

If every `χ ∈ Irr G` satisfied `χ x = χ 1`, then the non-conjugate case of column orthogonality
(`Work.CharCore.column_orthogonality_not_conj`, applied to the pair `(x, 1)`) together with the
reality of the degrees (`Complex.conj_natCast`) would give `∑ χ, χ(1)² = 0`, contradicting the
sum-of-degree-squares identity `Work.CharCore.sum_irr_degree_sq` (`∑ χ, χ(1)² = |G| ≠ 0`). -/
theorem exists_irr_apply_ne_one {G : Type} [Group G] [Fintype G] {x : G} (hx : x ≠ 1) :
    ∃ χ ∈ Work.CharCore.Irr G, χ x ≠ χ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hnc : ¬ IsConj x 1 := by
    intro hc
    obtain ⟨c, hc'⟩ := isConj_iff.mp hc
    apply hx
    have h2 : x = c⁻¹ * (c * x * c⁻¹) * c := by group
    rw [hc'] at h2
    simpa using h2
  have h1 := Work.CharCore.column_orthogonality_not_conj (g := x) (h := 1) hnc
  have h3 : ∑ χ ∈ Work.CharCore.Irr G, χ 1 ^ 2 = 0 := by
    rw [← h1]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hcon χ hχ, Work.CharCore.irrDeg_spec hχ, Complex.conj_natCast, pow_two]
  rw [Work.CharCore.sum_irr_degree_sq] at h3
  exact (Nat.cast_ne_zero.mpr (Nat.card_pos.ne')) h3

/-- **A non-trivial linear character of `Q₁` produces an element of `Q₁` outside `⁅Q,Q⁆`.**

`hlin` supplies `θ ∈ Irr Q₁` of degree one, i.e. a non-trivial homomorphism `φ : Q₁ →* ℂˣ`.
Since `Q = S · Q₁` is the direct product of `S` and `Q₁`, `φ` extends to `Φ : Q →* ℂˣ` by
`Φ(a·b) = φ b`; a homomorphism into the abelian group `ℂˣ` is trivial on commutators, so
`⁅Q,Q⁆ ≤ ker Φ`.  As `Φ` restricts to `φ` on `Q₁`, any `y ∈ Q₁` with `φ y ≠ 1` (which exists
because `θ ≠ 1`) cannot lie in `⁅Q,Q⁆`. -/
private theorem exists_mem_Q1_notMem_FSQcomm {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G)
    (hlin : ∃ theta ∈ Work.CharCore.Irr ↥h.Q1,
      theta 1 = 1 ∧ theta ≠ (fun _ : ↥h.Q1 => (1 : ℂ))) :
    ∃ x : G, x ∈ h.Q1 ∧ x ∉ FSQcomm h := by
  classical
  obtain ⟨θ, hθIrr, hθ1, hθne⟩ := hlin
  have hdeg : Work.CharCore.irrDeg θ = 1 := by
    have h' : ((Work.CharCore.irrDeg θ : ℕ) : ℂ) = 1 := by
      rw [← hθ1]; exact (Work.CharCore.irrDeg_spec hθIrr).symm
    exact_mod_cast h'
  obtain ⟨φ, hφ⟩ := (Work.CharCore.linear_char_iff_deg_one hθIrr).mp hdeg
  have hex : ∃ y : ↥h.Q1, φ y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hθne
    funext y
    rw [hφ y, hcon y]
    simp
  obtain ⟨y, hy⟩ := hex
  -- the extension `Φ : Q →* ℂˣ` of `φ` along `Q ≅ S × Q₁`
  let Φ : ↥h.Q →* ℂˣ :=
    { toFun := fun q => φ (h.prodIso.symm q).2
      map_one' := by show φ (h.prodIso.symm (1 : ↥h.Q)).2 = 1; rw [map_one]; simp
      map_mul' := fun q q' => by
        show φ (h.prodIso.symm (q * q')).2 = φ (h.prodIso.symm q).2 * φ (h.prodIso.symm q').2
        rw [map_mul, Prod.snd_mul, map_mul] }
  have hsymm : h.prodIso.symm ⟨(y : G), h.Q1_le_Q y.2⟩ = ((1 : ↥h.S), y) := by
    apply h.prodIso.injective
    rw [MulEquiv.apply_symm_apply]
    exact Subtype.ext (by simp [Work.FeitSibley.FSData.prodIso_apply,
      Work.FeitSibley.FSData.prodHom_apply])
  have hΦy : Φ ⟨(y : G), h.Q1_le_Q y.2⟩ = φ y := by
    show φ (h.prodIso.symm ⟨(y : G), h.Q1_le_Q y.2⟩).2 = φ y
    rw [hsymm]
  have hker : ⁅(⊤ : Subgroup ↥h.Q), (⊤ : Subgroup ↥h.Q)⁆ ≤ Φ.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm (Φ a) (Φ b))
  have hle : ⁅h.Q, h.Q⁆ ≤ Subgroup.map (Subgroup.subtype h.Q)
      (⁅(⊤ : Subgroup ↥h.Q), (⊤ : Subgroup ↥h.Q)⁆ : Subgroup ↥h.Q) := by
    rw [Subgroup.map_commutator (⊤ : Subgroup ↥h.Q) (⊤ : Subgroup ↥h.Q) (Subgroup.subtype h.Q)]
    refine Subgroup.commutator_mono ?_ ?_ <;> intro z hz <;> exact ⟨⟨z, hz⟩, trivial, rfl⟩
  refine ⟨(y : G), y.2, ?_⟩
  intro hyQ'
  have hxbar : (⟨(y : G), h.Q1_le_Q y.2⟩ : ↥h.Q) ∈
      ⁅(⊤ : Subgroup ↥h.Q), (⊤ : Subgroup ↥h.Q)⁆ := by
    obtain ⟨n, hn, hny⟩ := Subgroup.mem_map.mp (hle hyQ')
    have hn' : n = ⟨(y : G), h.Q1_le_Q y.2⟩ := Subtype.ext hny
    rwa [hn'] at hn
  have h1 : Φ ⟨(y : G), h.Q1_le_Q y.2⟩ = 1 := hker hxbar
  rw [hΦy] at h1
  exact hy h1

/-- **`𝒮(Q')` is non-empty when `Q₁` has a non-trivial linear character** (Peterfalvi II,
Appendice XII, p. 288).

Let `y ∈ Q₁ ∖ Q'` (`exists_mem_Q1_notMem_FSQcomm`) and let `ū ≠ 1` be its image in the finite
group `K = H ⧸ Q'` (`Q' ⊴ H` by `H_le_normalizer_FSQcomm`).  Characters separate points, so
there is `χ' ∈ Irr K` with `χ' ū ≠ χ' 1`.  Its inflation `χ = inflateFun Q' χ'` to `H`
(`Work.CohApps.inflateFun_mem_Irr`) is an irreducible character of `H` which is trivial on `Q'`
(`Work.CohApps.inflateFun_mem_charKernel`) and non-trivial at `y ∈ Q₁`, hence lies in
`𝒮(Q') = scriptSR h.H h.Q₁ Q'`. -/
theorem scriptSR_Qcomm_nonempty {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (hlin : ∃ theta ∈ Work.CharCore.Irr ↥h.Q1,
      theta 1 = 1 ∧ theta ≠ (fun _ : ↥h.Q1 => (1 : ℂ))) :
    (Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSQcomm h)).Nonempty := by
  classical
  obtain ⟨x, hxQ1, hxQ'⟩ := exists_mem_Q1_notMem_FSQcomm h hlin
  have hnorm := H_le_normalizer_FSQcomm h
  -- the quotient `K = H ⧸ Q'`
  let N : Subgroup ↥h.H := (FSQcomm h).subgroupOf h.H
  haveI hN : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  haveI hFint : Fintype (↥h.H ⧸ N) := QuotientGroup.fintype N
  let xH : ↥h.H := ⟨x, h.Q1_le_H hxQ1⟩
  have hxN : xH ∉ N := by
    rw [Subgroup.mem_subgroupOf]; exact hxQ'
  have hxne : (QuotientGroup.mk (s := N) xH) ≠ 1 := by
    intro hc
    exact hxN ((QuotientGroup.eq_one_iff xH).mp hc)
  obtain ⟨χ', hχ'Irr, hχ'ne⟩ := exists_irr_apply_ne_one (G := ↥h.H ⧸ N) hxne
  refine ⟨Work.Clifford.inflateFun N χ', ?_⟩
  rw [mem_scriptSR_iff]
  constructor
  · -- `χ = inflateFun N χ'` is in `𝒮`: it is the inflation of an irreducible and is
    -- non-trivial at `xH`
    have hIrr : Work.Clifford.inflateFun N χ' ∈ Work.CharCore.Irr ↥h.H :=
      Work.CohApps.inflateFun_mem_Irr N hχ'Irr
    have hwit : ∃ y : ↥h.H, (y : G) ∈ h.Q1 ∧
        Work.Clifford.inflateFun N χ' y ≠ Work.Clifford.inflateFun N χ' 1 := by
      refine ⟨xH, hxQ1, ?_⟩
      have h1 : Work.Clifford.inflateFun N χ' xH = χ' (QuotientGroup.mk (s := N) xH) := rfl
      have h2 : Work.Clifford.inflateFun N χ' (1 : ↥h.H) = χ' 1 := by
        show χ' (QuotientGroup.mk (s := N) (1 : ↥h.H)) = χ' 1
        rw [QuotientGroup.mk_one]
      rw [h1, h2]
      exact hχ'ne
    simp only [Work.FeitSibley.scriptS, Submission.Blueprint.excludingKernel, Finset.mem_filter]
    exact ⟨hIrr, hwit⟩
  · -- ... and trivial on `Q'`
    intro z hzQ'
    have hzN : z ∈ N := by
      rw [Subgroup.mem_subgroupOf]; exact hzQ'
    exact Work.CohApps.inflateFun_mem_charKernel N χ' hzN

end

end Work.FeitSibley.Coherence
