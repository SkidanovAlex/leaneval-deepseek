/-
# Free groups are separated by finite `p`-groups

Every nontrivial element of a finitely generated free group survives in some finite `p`-group
quotient, for every prime `p` (a free group is *residually a finite `p`-group*).

The proof is the classical ping-pong argument, made explicit:  for the parabolic matrices

* `Amat p = !![[1, p], [0, 1]]`, `Bmat p = !![[1, 0], [p, 1]]`

of `SL(2, ℤ)` (of determinant one, and congruent to the identity modulo `p`), the conjugates
`gmat p j = A^j B A^{-j}` have pairwise disjoint "ping-pong sets" `pset p j` (the open unit disc
around the cusp `p*j` inside the upper half plane) such that every nonzero power of `gmat p j` maps
the complement of `pset p j` into `pset p j`; there is even a point outside all of them.  The
ping-pong lemma (`pingpong_lift_injective`) therefore makes the elements `gmat p j` free generators
of a free subgroup of `SL(2, ℤ)`, so any `w ≠ 1` has nontrivial image in `SL(2, ℤ)`.

Finally, the principal congruence subgroup `SL(2, ℤ/p^k) → SL(2, ℤ/p)` is a finite `p`-group
(`isPGroup_congruence_sl2`), it contains the image of every `gmat p j`, and for `k` large enough the
image of `w` in `SL(2, ℤ/p^k)` is nontrivial.
-/
import Mathlib
import Submission.Work.ORLocInd.Basic
import Submission.Work.ORLocInd.FKS.SL2Defs
import Submission.Work.ORLocInd.FKS.SL2Geom
import Submission.Work.ORLocInd.FKS.pingpong_lift_injective
import Submission.Work.ORLocInd.FKS.norm_div_affine_lt_one
import Submission.Work.ORLocInd.FKS.isPGroup_congruence_sl2
import Submission.Work.ORLocInd.FKS.pset_disjoint
import Submission.Work.ORLocInd.FKS.exists_notMem_pset

namespace Work.ORLocInd.FKS

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

/-! ## The ping-pong condition for the family `gmat p j` -/

/-- Every nonzero power of `gmat p j` maps the complement of the ping-pong set `pset p j` into
`pset p j`.  Indeed `(gmat p j) ^ k` acts on the upper half plane by
`z ↦ (z - p*j)/(p*k*(z - p*j) + 1) + p*j`, and `‖w/(N*w+1)‖ < 1` whenever `w.im ≠ 0`, `‖w‖ ≥ 1` and
`|N| ≥ 2`. -/
lemma gmat_pset_compl (p : ℕ) (hp : 2 ≤ p) (j : ℕ) (k : ℤ) (hk : k ≠ 0) :
    ∀ z : UpperHalfPlane, z ∉ pset p j → (gmat p j ^ k) • z ∈ pset p j := by
  intro z hz
  have hz' : (1 : ℝ) ≤ ‖(↑z : ℂ) - (p * j : ℂ)‖ := by
    simpa [pset, not_lt] using hz
  show ‖(↑((gmat p j ^ k) • z) : ℂ) - (p * j : ℂ)‖ < 1
  have hsub : (↑((gmat p j ^ k) • z) : ℂ) - (p * j : ℂ) =
      ((↑z : ℂ) - (p * j : ℂ)) / (↑((p : ℤ) * k) * ((↑z : ℂ) - (p * j : ℂ)) + 1) := by
    rw [coe_gmat_pow_smul]; push_cast; ring
  rw [hsub]
  refine norm_div_affine_lt_one (w := (↑z : ℂ) - (p * j : ℂ)) (N := (p : ℤ) * k) ?_ ?_ ?_
  · have h : ((↑z : ℂ) - (p * j : ℂ)).im = z.im := by simp
    rw [h]; exact z.im_ne_zero
  · exact hz'
  · have hk1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
    have hp' : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (p : ℤ))]
    calc (2 : ℤ) ≤ (p : ℤ) * 1 := by linarith
      _ ≤ (p : ℤ) * |k| := mul_le_mul_of_nonneg_left hk1 (by positivity)

/-! ## Reduction modulo `p` -/

private lemma map_Amat_eq_one (p : ℕ) :
    ((SpecialLinearGroup.map (Int.castRingHom (ZMod p)) (Amat p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 := by
  ext i l
  rw [sl_map_apply]
  fin_cases i <;> fin_cases l <;> simp [Amat, Matrix.one_apply, ZMod.natCast_self]

private lemma map_Bmat_eq_one (p : ℕ) :
    ((SpecialLinearGroup.map (Int.castRingHom (ZMod p)) (Bmat p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 := by
  ext i l
  rw [sl_map_apply]
  fin_cases i <;> fin_cases l <;> simp [Bmat, Matrix.one_apply, ZMod.natCast_self]

private lemma map_gmat_eq_one (p : ℕ) (j : ℕ) :
    SpecialLinearGroup.map (Int.castRingHom (ZMod p)) (gmat p j) = 1 := by
  rw [show gmat p j = Amat p ^ (j : ℤ) * Bmat p * (Amat p ^ (j : ℤ))⁻¹ from rfl,
    map_mul, map_mul, map_zpow, map_inv, map_zpow,
    show SpecialLinearGroup.map (Int.castRingHom (ZMod p)) (Amat p) = 1 from
      Subtype.ext (map_Amat_eq_one p),
    show SpecialLinearGroup.map (Int.castRingHom (ZMod p)) (Bmat p) = 1 from
      Subtype.ext (map_Bmat_eq_one p)]
  simp

private lemma castHom_comp (p k : ℕ) (h : p ∣ p^k) :
    (ZMod.castHom h (ZMod p)).comp (Int.castRingHom (ZMod (p^k))) =
      Int.castRingHom (ZMod p) := by
  ext m
  rw [RingHom.comp_apply, ZMod.castHom_apply]
  exact ZMod.cast_intCast h m

/-! ## The main theorem -/

theorem freeGroup_separated_by_finite_p_group {α : Type*} [Fintype α] {p : ℕ} (hp : p.Prime)
    (w : FreeGroup α) (hw : w ≠ 1) :
    ∃ (Q : Type*) (_ : Group Q) (_ : Finite Q) (_ : IsPGroup p Q) (ψ : FreeGroup α →* Q),
      ψ w ≠ 1 := by
  classical
  by_cases hα : Nonempty α
  swap
  · -- `α` empty: the free group on `α` is trivial
    exfalso
    haveI : IsEmpty α := not_nonempty_iff.mp hα
    refine hw ?_
    have hnt : w.toWord = [] := List.eq_nil_iff_forall_not_mem.mpr (fun x _ => IsEmpty.false x.1)
    rw [← FreeGroup.mk_toWord (x := w), hnt, ← FreeGroup.one_eq_mk]
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : p ≠ 0 := hp.pos.ne'
  -- enumerate the generators of `FreeGroup α`
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let g : α → SL(2, ℤ) := fun a => gmat p (e a).val
  let S : α → Set ℍ := fun a => pset p (e a).val
  obtain ⟨x, hx0⟩ := exists_notMem_pset p
  -- the ping-pong lemma: the generators are free
  have hinj : Function.Injective (FreeGroup.lift g) :=
    pingpong_lift_injective g
      (fun a1 a2 ha => pset_disjoint p hp2 (fun hh => ha (e.injective (Fin.ext hh))))
      (fun a k hk z hz => gmat_pset_compl p hp2 (e a).val k hk z hz)
      (fun a => hx0 _)
  have hu : FreeGroup.lift g w ≠ 1 := fun h => hw (hinj h)
  -- some entry of the image of `w` is not the corresponding entry of the identity
  obtain ⟨i, jj, hij⟩ : ∃ i jj : Fin 2, (FreeGroup.lift g w) i jj ≠ (1 : SL(2, ℤ)) i jj := by
    by_contra hcon
    push_neg at hcon
    exact hu (Matrix.SpecialLinearGroup.ext _ _ hcon)
  set c : ℤ := (FreeGroup.lift g w) i jj - (1 : SL(2, ℤ)) i jj with hcdef
  have hc0 : c ≠ 0 := by rw [hcdef]; exact sub_ne_zero.mpr hij
  -- choose `k` with `p^k ∤ c`
  have hkexists : ∃ k : ℕ, 1 ≤ k ∧ ¬ ((p : ℤ)^k ∣ c) := by
    refine ⟨c.natAbs + 1, by omega, ?_⟩
    intro hdvd
    have hlt : (c.natAbs : ℤ) < (p : ℤ)^(c.natAbs + 1) := by
      have h1 : c.natAbs < 2 ^ (c.natAbs + 1) := by
        calc c.natAbs < 2 ^ c.natAbs := Nat.lt_two_pow_self
          _ ≤ 2 ^ (c.natAbs + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ (c.natAbs + 1) ≤ p ^ (c.natAbs + 1) := Nat.pow_le_pow_left hp2 _
      exact_mod_cast lt_of_lt_of_le h1 h2
    have hdvd' : (p : ℤ)^(c.natAbs + 1) ∣ (c.natAbs : ℤ) := Int.dvd_natAbs.mpr hdvd
    have hpos : (0 : ℤ) < (c.natAbs : ℤ) := by exact_mod_cast Int.natAbs_pos.mpr hc0
    have hle : (p : ℤ)^(c.natAbs + 1) ≤ (c.natAbs : ℤ) := Int.le_of_dvd hpos hdvd'
    linarith
  obtain ⟨k, hk1, hkndvd⟩ := hkexists
  have hdiv : p ∣ p^k := ⟨p^(k-1), by rw [← pow_succ', Nat.sub_add_cancel hk1]⟩
  haveI : NeZero (p^k) := ⟨pow_ne_zero _ hp0⟩
  haveI : NeZero p := ⟨hp0⟩
  set ρ : SL(2, ZMod (p^k)) →* SL(2, ZMod p) :=
    SpecialLinearGroup.map (ZMod.castHom hdiv (ZMod p)) with hρ
  -- every generator maps into the kernel of the reduction
  have hgen : ∀ a : α,
      SpecialLinearGroup.map (Int.castRingHom (ZMod (p^k))) (g a) ∈ MonoidHom.ker ρ := by
    intro a
    show ρ (SpecialLinearGroup.map (Int.castRingHom (ZMod (p^k))) (gmat p (e a).val)) = 1
    rw [hρ, sl_map_map, castHom_comp p k hdiv]
    exact map_gmat_eq_one p (e a).val
  -- we lift to a larger universe because the existential is stated with `Type*`
  haveI : Finite (MonoidHom.ker ρ) := inferInstance
  let ψ : FreeGroup α →* ULift (MonoidHom.ker ρ) :=
    (MulEquiv.ulift.symm : MonoidHom.ker ρ ≃* ULift (MonoidHom.ker ρ)).toMonoidHom.comp
      (FreeGroup.lift (fun a => (⟨SpecialLinearGroup.map (Int.castRingHom (ZMod (p^k))) (g a),
        hgen a⟩ : MonoidHom.ker ρ)))
  refine ⟨ULift (MonoidHom.ker ρ), inferInstance, ?_, ?_, ψ, ?_⟩
  · exact Finite.of_injective
      (Equiv.ulift : ULift (MonoidHom.ker ρ) ≃ MonoidHom.ker ρ) Equiv.ulift.injective
  · exact (isPGroup_congruence_sl2 p k hp hdiv).of_equiv (MulEquiv.ulift.symm)
  · -- the image of `w` is nontrivial
    intro hcon
    have hcon₀ : (FreeGroup.lift (fun a => (⟨SpecialLinearGroup.map (Int.castRingHom (ZMod (p^k))) (g a),
        hgen a⟩ : MonoidHom.ker ρ))) w = 1 := by
      have h := congrArg (fun y : ULift (MonoidHom.ker ρ) =>
        (MulEquiv.ulift y : MonoidHom.ker ρ)) hcon
      simpa [ψ, MonoidHom.comp_apply] using h
    have hhom : (Subgroup.subtype (MonoidHom.ker ρ)).comp
        (FreeGroup.lift (fun a => (⟨SpecialLinearGroup.map (Int.castRingHom (ZMod (p^k))) (g a),
          hgen a⟩ : MonoidHom.ker ρ))) =
        FreeGroup.lift (fun a => SpecialLinearGroup.map (Int.castRingHom (ZMod (p^k))) (g a)) := by
      apply FreeGroup.ext_hom
      intro a
      simp [FreeGroup.lift_apply_of]
    have hcon' : FreeGroup.lift (fun a => SpecialLinearGroup.map (Int.castRingHom (ZMod (p^k))) (g a))
        w = 1 := by
      rw [← hhom]
      simpa using congrArg (fun y : MonoidHom.ker ρ => (y : SL(2, ZMod (p^k)))) hcon₀
    have hcomm : FreeGroup.lift (fun a => SpecialLinearGroup.map (Int.castRingHom (ZMod (p^k))) (g a)) =
        (SpecialLinearGroup.map (Int.castRingHom (ZMod (p^k)))).comp (FreeGroup.lift g) := by
      apply FreeGroup.ext_hom
      intro a
      rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
    rw [hcomm, MonoidHom.comp_apply] at hcon'
    have hone : (1 : SL(2, ZMod (p^k))) i jj = (((1 : SL(2, ℤ)) i jj : ℤ) : ZMod (p^k)) := by
      fin_cases i <;> fin_cases jj <;> simp [Matrix.one_apply]
    have h2 := congrArg (fun M : SL(2, ZMod (p^k)) => M i jj) hcon'
    rw [hone] at h2
    have h3 : ((FreeGroup.lift g w) i jj : ZMod (p^k)) =
        (((1 : SL(2, ℤ)) i jj : ℤ) : ZMod (p^k)) := by
      rw [← h2]; rfl
    have hne : ((c : ℤ) : ZMod (p^k)) ≠ 0 := by
      intro hh
      exact hkndvd ((ZMod.intCast_zmod_eq_zero_iff_dvd c (p^k)).mp hh)
    exact hne (by rw [hcdef]; push_cast; rw [h3]; ring)

end Work.ORLocInd.FKS
