import Mathlib
import Submission.Work.BW.BWGradedBase
import Submission.Work.BW.multiHom_assPrime

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

variable {N : ℕ}

/-- The colon of `J` by `x` is the annihilator of the image of `x` in `R ⧸ J`. -/
private theorem colonSpan_eq_colon_mk (J : Ideal (MR N)) (x : MR N) :
    colonSpan J x =
      (⊥ : Submodule (MR N) (MR N ⧸ J)).colon {Ideal.Quotient.mk J x} := by
  rw [colonSpan, Submodule.bot_colon', ← Submodule.annihilator_map_mkQ_eq_colon, Submodule.map_span]
  congr 1
  simp [Set.image_singleton]

/-- `colonSpan J 1 = J`. -/
private theorem colonSpan_one (J : Ideal (MR N)) : colonSpan J (1 : MR N) = J := by
  ext a
  rw [mem_colonSpan]
  simp

/-- An element whose multihomogeneous components all lie in `J` lies in `J`. -/
private theorem mem_of_components_mem {J : Ideal (MR N)} (hJ : MultiHomZ N J) {p : MR N}
    (h : ∀ u, weightedHomogeneousComponent (wZ N) u p ∈ J) : p ∈ J := by
  rw [← sum_weightedHomogeneousComponent (wZ N) p]
  rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp (w := wZ N) p)]
  exact Submodule.sum_mem J (fun u _ => h u)

/-- If `p ≤ (J : x)` with `J` and `p` multihomogeneous, then `p ≤ (J : x_u)` for every
multihomogeneous component `x_u` of `x`. -/
private theorem le_colon_component {J p : Ideal (MR N)} (hJ : MultiHomZ N J) (hp : MultiHomZ N p)
    {x : MR N} (h : p ≤ colonSpan J x) (u : Fin (N + 1) →₀ ℤ) :
    p ≤ colonSpan J (weightedHomogeneousComponent (wZ N) u x) := by
  intro f hf
  rw [mem_colonSpan]
  refine mem_of_components_mem hJ (fun w => ?_)
  have hg : weightedHomogeneousComponent (wZ N) (w - u) f ∈ p := hp f hf (w - u)
  have hgx : weightedHomogeneousComponent (wZ N) (w - u) f * x ∈ J := by
    have := h hg
    rwa [mem_colonSpan] at this
  have hcomp := comp_mul_of_mem (weightedHomogeneousComponent_mem (wZ N) f (w - u)) x w
  rw [show w - (w - u) = u from by abel] at hcomp
  rw [mul_comm f (weightedHomogeneousComponent (wZ N) u x),
    comp_mul_of_mem (weightedHomogeneousComponent_mem (wZ N) x u) f w,
    mul_comm (weightedHomogeneousComponent (wZ N) u x)
      (weightedHomogeneousComponent (wZ N) (w - u) f),
    ← hcomp]
  exact hJ _ hgx w

/-- Every associated prime of `R ⧸ J` is a colon of `J`. -/
private theorem ass_mem_colon (J : Ideal (MR N)) {Q : Ideal (MR N)}
    (hQ : Q ∈ associatedPrimes (MR N) (MR N ⧸ J)) :
    ∃ y : MR N, y ∉ J ∧ Q = colonSpan J y := by
  have hQ' := hQ
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hQ'
  obtain ⟨hQprime, y, hyQ⟩ := hQ'
  obtain ⟨y', rfl⟩ := Submodule.mkQ_surjective J y
  have hy_ne : y' ∉ J := by
    intro hmem
    have hy0 : Submodule.mkQ J y' = 0 := by
      rw [Submodule.mkQ_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [hyQ, hy0, Submodule.colon_singleton_zero] at hQprime
    exact hQprime.1 rfl
  exact ⟨y', hy_ne, by rw [hyQ]; exact (colonSpan_eq_colon_mk J y').symm⟩

theorem homogeneous_colon_prime {N : ℕ} (J : Ideal (MR N)) (hJ : MultiHomZ N J)
    (h : J ≠ ⊤) :
    ∃ (d : Fin (N + 1) →₀ ℕ) (x : MR N), x ∈ homPiece N d ∧ x ∉ J ∧
      (colonSpan J x).IsPrime ∧ MultiHomZ N (colonSpan J x) ∧ J ≤ colonSpan J x := by
  classical
  have h1J : (1 : MR N) ∉ J := fun hmem => h ((Ideal.eq_top_iff_one J).mpr hmem)
  -- the family of colons of `J`
  set S : Set (Ideal (MR N)) := {q | ∃ x : MR N, x ∉ J ∧ q = colonSpan J x} with hS_def
  have hS_ne : S.Nonempty := ⟨J, 1, h1J, (colonSpan_one J).symm⟩
  obtain ⟨p, hp_max⟩ :=
    WellFoundedGT.exists_maximal (inferInstance : WellFoundedGT (Ideal (MR N))) S hS_ne
  have hpS : p ∈ S := hp_max.1
  have hpmax : ∀ b ∈ S, p ≤ b → b ≤ p := hp_max.2
  obtain ⟨x, hxJ, hpx⟩ := hpS
  -- `p` is prime
  have hp_ne_top : p ≠ ⊤ := by
    intro htop
    have h1p : (1 : MR N) ∈ p := htop ▸ Submodule.mem_top
    rw [hpx, mem_colonSpan] at h1p
    exact hxJ (by simpa using h1p)
  have hp_prime : p.IsPrime := by
    rw [Ideal.isPrime_iff]
    refine ⟨hp_ne_top, ?_⟩
    intro a b hab
    by_cases ha : a ∈ p
    · exact Or.inl ha
    · refine Or.inr ?_
      have haxJ : a * x ∉ J := fun hmem => ha (by rw [hpx, mem_colonSpan]; exact hmem)
      have hle : p ≤ colonSpan J (a * x) := by
        intro f hf
        rw [mem_colonSpan]
        have hfx : f * x ∈ J := by
          have := hpx.le hf
          rwa [mem_colonSpan] at this
        have h1 : f * (a * x) = a * (f * x) := by ring
        rw [h1]
        exact J.mul_mem_left a hfx
      have hb_le : colonSpan J (a * x) ≤ p := hpmax _ ⟨a * x, haxJ, rfl⟩ hle
      have hab' : a * b * x ∈ J := by
        have := hpx.le hab
        rwa [mem_colonSpan] at this
      refine hb_le ?_
      rw [mem_colonSpan]
      have h2 : b * (a * x) = a * b * x := by ring
      rw [h2]
      exact hab'
  -- `p` is an associated prime of `R ⧸ J`, hence multihomogeneous
  have hp_ass : p ∈ associatedPrimes (MR N) (MR N ⧸ J) := by
    rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff]
    exact ⟨hp_prime, ⟨Ideal.Quotient.mk J x, by rw [hpx]; exact colonSpan_eq_colon_mk J x⟩⟩
  have hp_hom : MultiHomZ N p :=
    (multiHom_iff_multiHomZ p).mp
      (multiHom_assPrime J ((multiHom_iff_multiHomZ J).mpr hJ) p hp_ass)
  -- a multihomogeneous component of `x` not in `J`
  have hcomp : ∃ u, weightedHomogeneousComponent (wZ N) u x ∉ J := by
    by_contra hcon
    push_neg at hcon
    exact hxJ (mem_of_components_mem hJ hcon)
  obtain ⟨u, huJ⟩ := hcomp
  have hxu_piece : weightedHomogeneousComponent (wZ N) u x ∈ pieceZ N u :=
    weightedHomogeneousComponent_mem (wZ N) x u
  have hxu_ne : weightedHomogeneousComponent (wZ N) u x ≠ 0 := by
    intro h0
    exact huJ (by rw [h0]; exact J.zero_mem)
  obtain ⟨d, hd⟩ : ∃ d : Fin (N + 1) →₀ ℕ, castF d = u := by
    by_contra hcon
    push_neg at hcon
    rw [pieceZ_eq_bot_of_not_mem_range (N := N) (u := u) hcon, Submodule.mem_bot] at hxu_piece
    exact hxu_ne hxu_piece
  -- the component realises the same colon
  have hle2 : p ≤ colonSpan J (weightedHomogeneousComponent (wZ N) u x) :=
    le_colon_component hJ hp_hom hpx.le u
  have hle1 : colonSpan J (weightedHomogeneousComponent (wZ N) u x) ≤ p := by
    have hxu0 : Ideal.Quotient.mk J (weightedHomogeneousComponent (wZ N) u x) ≠ 0 := by
      rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact huJ
    obtain ⟨Q, hQass, hQle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing
      (R := MR N) (M := MR N ⧸ J) (Ideal.Quotient.mk J (weightedHomogeneousComponent (wZ N) u x)) hxu0
    have hQ_ge : colonSpan J (weightedHomogeneousComponent (wZ N) u x) ≤ Q := by
      rw [colonSpan_eq_colon_mk]
      exact hQle
    obtain ⟨y, hyJ, hQy⟩ := ass_mem_colon J hQass
    exact hQ_ge.trans (hpmax Q ⟨y, hyJ, hQy⟩ (hle2.trans hQ_ge))
  have hcolon : colonSpan J (weightedHomogeneousComponent (wZ N) u x) = p := le_antisymm hle1 hle2
  refine ⟨d, weightedHomogeneousComponent (wZ N) u x, ?_, huJ, ?_, ?_, le_colonSpan J _⟩
  · rw [homPiece_eq_pieceZ, hd]
    exact hxu_piece
  · rw [hcolon]; exact hp_prime
  · rw [hcolon]; exact hp_hom

end Work.BW
