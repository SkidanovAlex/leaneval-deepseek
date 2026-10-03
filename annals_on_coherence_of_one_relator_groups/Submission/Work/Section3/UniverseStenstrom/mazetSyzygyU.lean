/-
# Mazet's syzygy lemma at an arbitrary universe

This file re-proves, in an arbitrary universe `u`, the group-theoretic input of Mazet's
presentation theorem: a relation `∑_s s ⊗ t_s + 1 ⊗ ts = 0` in the `R`-balanced tensor product
`S ⊗[R] S` (see `Work.ORHughesFree.Epic.BalancedTensor`) is *generated* by Mazet's elementary
relations, i.e. there are finitely many "columns" `mu` with

* `∑_s s * f (a mu s) + f (astar mu) = 0`   (a relation over `R`),
* `t s = ∑_mu f (a mu s) * z mu` and `ts = ∑_mu f (astar mu) * z mu`,

so that the element `(t, ts)` of `(S →₀ S) × S` lies in the subgroup `MazetU.Rel f` of Mazet
presentations.

The proof is a universe-general transcription of the argument of
`Submission.Work.ORHughesFree.Section3.mazetPresentation` (namespace `Mazet`), which lives at
universe `0`; `Section3` needs it for rings in an arbitrary fixed universe `u`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Epic.BalancedTensor

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.Section3.UniverseStenstrom

open Work.ORHughesFree.Epic (BalancedTensor)
open scoped TensorProduct

namespace MazetU

variable {R S : Type u} [Ring R] [Ring S]

/-! ### The elementary relation attached to `c : S →₀ R` and `y : S` -/

/-- `relElem f c y` is the finitely supported function `s ↦ f (c s) * y`. -/
noncomputable def relElem (f : R →+* S) (c : S →₀ R) (y : S) : S →₀ S :=
  (c.mapRange f (map_zero f)).mapRange (fun x => x * y) (zero_mul y)

lemma relElem_apply (f : R →+* S) (c : S →₀ R) (y : S) (a : S) :
    relElem f c y a = f (c a) * y := by
  classical
  simp [relElem, Finsupp.mapRange_apply]

lemma relElem_single (f : R →+* S) (a : S) (r : R) (y : S) :
    relElem f (Finsupp.single a r) y = Finsupp.single a (f r * y) := by
  classical
  ext b
  rw [relElem_apply, Finsupp.single_apply, Finsupp.single_apply]
  by_cases h : a = b <;> simp [h]

lemma relElem_sub (f : R →+* S) (c c' : S →₀ R) (y : S) :
    relElem f (c - c') y = relElem f c y - relElem f c' y := by
  classical
  ext a
  rw [Finsupp.sub_apply, relElem_apply, relElem_apply, relElem_apply, Finsupp.sub_apply,
    map_sub, sub_mul]

/-! ### The subgroup `Rel f` of Mazet presentations -/

/-- The (additive) subgroup of `(S →₀ S) × S` consisting of the elements which "admit a Mazet
presentation": `x = (z, w)` lies in `Rel f` if there are finitely many columns `μ`, a family
`a μ : S →₀ R` (finitely supported), scalars `astar μ ∈ R` and elements `z μ ∈ S` with

* `∑_s s * f (a μ s) + f (astar μ) = 0` (the relations),
* `z s = ∑_μ f (a μ s) * z μ` for all `s`,
* `w = ∑_μ f (astar μ) * z μ`.

The second factor `S` of the product models the extra generator `★ ↦ 1` of Mazet's
argument. -/
noncomputable def Rel (f : R →+* S) : AddSubgroup ((S →₀ S) × S) where
  carrier := {x | ∃ (m : ℕ) (a : Fin m → S →₀ R) (astar : Fin m → R) (z : Fin m → S),
      (∀ μ, (a μ).sum (fun a r => a * f r) + f (astar μ) = 0) ∧
      (∀ b, x.1 b = ∑ μ, f (a μ b) * z μ) ∧
      (x.2 = ∑ μ, f (astar μ) * z μ)}
  zero_mem' := by
    refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
    · intro μ; exact μ.elim0
    · intro b; simp
    · simp
  add_mem' := by
    rintro x y ⟨m, a, astar, z, hrel, hx1, hx2⟩ ⟨m', a', astar', z', hrel', hy1, hy2⟩
    have key : ∀ b : S, (∑ μ : Fin (m+m'), f ((Fin.append a a' μ) b) * Fin.append z z' μ)
        = (∑ i : Fin m, f (a i b) * z i) + (∑ i : Fin m', f (a' i b) * z' i) := by
      intro b
      rw [Fin.sum_univ_add]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_left, Fin.append_left]
      · exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_right, Fin.append_right]
    have key2 : (∑ μ : Fin (m+m'), f ((Fin.append astar astar') μ) * Fin.append z z' μ)
        = (∑ i : Fin m, f (astar i) * z i) + (∑ i : Fin m', f (astar' i) * z' i) := by
      rw [Fin.sum_univ_add]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_left, Fin.append_left]
      · exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_right, Fin.append_right]
    refine ⟨m + m', Fin.append a a', Fin.append astar astar', Fin.append z z', ?_, ?_, ?_⟩
    · intro μ
      refine Fin.addCases (motive := fun μ => ((Fin.append a a') μ).sum (fun a r => a * f r)
        + f ((Fin.append astar astar') μ) = 0) (fun i => ?_) (fun i => ?_) μ
      · rw [Fin.append_left, Fin.append_left]; exact hrel i
      · rw [Fin.append_right, Fin.append_right]; exact hrel' i
    · intro b
      rw [Prod.fst_add, Finsupp.add_apply, hx1 b, hy1 b, key b]
    · rw [Prod.snd_add, hx2, hy2, key2]
  neg_mem' := by
    rintro x ⟨m, a, astar, z, hrel, hx1, hx2⟩
    refine ⟨m, a, astar, fun μ => -z μ, ?_, ?_, ?_⟩
    · intro μ; exact hrel μ
    · intro b
      rw [Prod.fst_neg, Finsupp.neg_apply, hx1 b, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_neg]
    · rw [Prod.snd_neg, hx2, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_neg]

/-- The elementary elements of `Rel f`: from a relation `c : S →₀ R` (with `∑_s s * f (c s) = 0`)
and an element `y : S` one obtains `(relElem f c y, 0) ∈ Rel f`. -/
lemma Rel_of_relElem (f : R →+* S) (c : S →₀ R) (y : S)
    (hc : c.sum (fun a r => a * f r) = 0) : (relElem f c y, 0) ∈ Rel f := by
  refine ⟨1, fun _ => c, fun _ => 0, fun _ => y, ?_, ?_, ?_⟩
  · intro μ; simpa using hc
  · intro b; rw [relElem_apply]; simp
  · simp

/-- The "additivity in the first variable" defect lies in `Rel f`. -/
lemma Rel_defect_add (f : R →+* S) (s s' t : S) :
    (Finsupp.single (s + s') t - Finsupp.single s t - Finsupp.single s' t, 0) ∈ Rel f := by
  have hsub : ∀ (a : S) (b₁ b₂ : R),
      (fun a r => a * f r) a (b₁ - b₂) = (fun a r => a * f r) a b₁ - (fun a r => a * f r) a b₂ := by
    intro a b₁ b₂; simp only; rw [map_sub, mul_sub]
  have hc : (Finsupp.single (s + s') (1 : R) - Finsupp.single s (1 : R)
      - Finsupp.single s' (1 : R)).sum (fun a r => a * f r) = 0 := by
    rw [Finsupp.sum_sub_index hsub, Finsupp.sum_sub_index hsub,
        Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp),
        Finsupp.sum_single_index (by simp)]
    simp
  have h := Rel_of_relElem f _ t hc
  simp only [relElem_sub, relElem_single, map_one, one_mul] at h
  exact h

/-- The "integer scaling in the first variable" defect lies in `Rel f`. -/
lemma Rel_defect_smul (f : R →+* S) (s t : S) (n : ℤ) :
    (Finsupp.single (n • s) t - Finsupp.single s (n • t), 0) ∈ Rel f := by
  have hsub : ∀ (a : S) (b₁ b₂ : R),
      (fun a r => a * f r) a (b₁ - b₂) = (fun a r => a * f r) a b₁ - (fun a r => a * f r) a b₂ := by
    intro a b₁ b₂; simp only; rw [map_sub, mul_sub]
  have hc : (Finsupp.single (n • s) (1 : R) - Finsupp.single s (↑n : R)).sum
      (fun a r => a * f r) = 0 := by
    rw [Finsupp.sum_sub_index hsub, Finsupp.sum_single_index (by simp),
        Finsupp.sum_single_index (by simp)]
    simp [map_intCast, zsmul_eq_mul, Int.cast_comm]
  have h := Rel_of_relElem f _ t hc
  simp only [relElem_sub, relElem_single, map_one, one_mul, map_intCast] at h
  rw [← zsmul_eq_mul] at h
  exact h

/-- The "balance" defect lies in `Rel f`. -/
lemma Rel_defect_balance (f : R →+* S) (s t : S) (r : R) :
    (Finsupp.single (s * f r) t - Finsupp.single s (f r * t), 0) ∈ Rel f := by
  have hsub : ∀ (a : S) (b₁ b₂ : R),
      (fun a r => a * f r) a (b₁ - b₂) = (fun a r => a * f r) a b₁ - (fun a r => a * f r) a b₂ := by
    intro a b₁ b₂; simp only; rw [map_sub, mul_sub]
  have hc : (Finsupp.single (s * f r) (1 : R) - Finsupp.single s r).sum
      (fun a r => a * f r) = 0 := by
    rw [Finsupp.sum_sub_index hsub, Finsupp.sum_single_index (by simp),
        Finsupp.sum_single_index (by simp)]
    simp
  have h := Rel_of_relElem f _ t hc
  simp only [relElem_sub, relElem_single, map_one, one_mul] at h
  exact h

/-- The extra generator `★` of Mazet's argument maps to `1 ∈ S`. -/
lemma Rel_single_one (f : R →+* S) (t : S) :
    (Finsupp.single (1 : S) t, -t) ∈ Rel f := by
  refine ⟨1, fun _ => Finsupp.single (1 : S) (1 : R), fun _ => -1, fun _ => t, ?_, ?_, ?_⟩
  · intro μ
    rw [Finsupp.sum_single_index (by simp), map_one, mul_one, map_neg, map_one]
    abel
  · intro b
    simp only [Fin.sum_univ_one]
    rw [← relElem_apply, relElem_single, map_one, one_mul]
  · simp only [Fin.sum_univ_one]
    rw [map_neg, map_one, neg_one_mul]

/-! ### The canonical map `θ : (S →₀ S) × S → BalancedTensor f` -/

/-- `tmul f a -` vanishes at `0`. -/
theorem bt_tmul_zero_right (f : R →+* S) (a : S) : BalancedTensor.tmul f a 0 = 0 := by
  show BalancedTensor.mk f (a ⊗ₜ[ℤ] (0 : S)) = 0
  rw [TensorProduct.tmul_zero, map_zero]

/-- `tmul f - t` vanishes at `0`. -/
theorem bt_tmul_zero_left (f : R →+* S) (t : S) : BalancedTensor.tmul f 0 t = 0 := by
  show BalancedTensor.mk f ((0 : S) ⊗ₜ[ℤ] t) = 0
  rw [TensorProduct.zero_tmul, map_zero]

/-- The additive homomorphism `v ↦ tmul f a v`. -/
noncomputable def tmulHom (f : R →+* S) (a : S) : S →+ BalancedTensor f where
  toFun v := BalancedTensor.tmul f a v
  map_zero' := bt_tmul_zero_right f a
  map_add' := fun v v' => BalancedTensor.tmul_add_right f a v v'

/-- The canonical map on the free part `S →₀ S`: the generators `s ↦ s ⊗ -`. -/
noncomputable def theta1 (f : R →+* S) : (S →₀ S) →+ BalancedTensor f :=
  Finsupp.liftAddHom (fun a => tmulHom f a)

lemma theta1_apply (f : R →+* S) (z : S →₀ S) :
    theta1 f z = z.sum (fun a v => BalancedTensor.tmul f a v) := by
  rw [theta1, Finsupp.liftAddHom_apply]
  rfl

/-- The extra generator `★ ↦ 1`. -/
noncomputable def theta2 (f : R →+* S) : S →+ BalancedTensor f := tmulHom f 1

/-- The canonical map `θ : (S →₀ S) × S → BalancedTensor f`, `(z, w) ↦ ∑_s s ⊗ z_s + 1 ⊗ w`. -/
noncomputable def theta (f : R →+* S) : ((S →₀ S) × S) →+ BalancedTensor f :=
  (theta1 f).comp (AddMonoidHom.fst _ _) + (theta2 f).comp (AddMonoidHom.snd _ _)

lemma theta_apply (f : R →+* S) (x : (S →₀ S) × S) :
    theta f x = theta1 f x.1 + BalancedTensor.tmul f 1 x.2 := rfl

/-! ### The inverse map on `((S →₀ S) × S) ⧸ Rel f` -/

/-- Pushforward of a finsupp sum along an additive map. -/
lemma map_finsupp_sum {A N N' : Type u} [AddCommMonoid A] [AddCommMonoid N] [AddCommMonoid N']
    (φ : N → N') (h0 : φ 0 = 0) (hadd : ∀ x y : N, φ (x + y) = φ x + φ y)
    (z : S →₀ A) (g : S → A → N) : φ (z.sum g) = z.sum (fun a v => φ (g a v)) := by
  rw [Finsupp.sum, Finsupp.sum]
  exact map_sum (⟨⟨φ, h0⟩, hadd⟩ : N →+ N') (fun a => g a (z a)) z.support

/-- The additive homomorphism `z ↦ (z, 0)`. -/
noncomputable def inlHom : (S →₀ S) →+ ((S →₀ S) × S) where
  toFun z := (z, 0)
  map_zero' := rfl
  map_add' z z' := by rw [Prod.mk_add_mk, add_zero]

/-- The bilinear map `(s, t) ↦ (single s t, 0)` modulo `Rel f`. -/
noncomputable def beta (f : R →+* S) : S →ₗ[ℤ] S →ₗ[ℤ] ((S →₀ S) × S) ⧸ Rel f :=
  LinearMap.mk₂ ℤ (fun s t => QuotientAddGroup.mk' (Rel f) (Finsupp.single s t, (0 : S)))
    (fun s s' t => by
      rw [← map_add]
      refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
      have h := Rel_defect_add f s s' t
      simpa [Prod.mk_add_mk, Prod.mk_sub_mk, sub_sub] using h)
    (fun n s t => by
      rw [← map_zsmul]
      rw [Prod.smul_mk, smul_zero, Finsupp.smul_single]
      refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
      have h := Rel_defect_smul f s t n
      simpa [Prod.mk_sub_mk] using h)
    (fun s t t' => by
      have key : ((Finsupp.single s t + Finsupp.single s t', (0:S)) : (S →₀ S) × S)
          = (Finsupp.single s t, (0:S)) + (Finsupp.single s t', (0:S)) := by
        rw [Prod.mk_add_mk, add_zero]
      rw [Finsupp.single_add, key, map_add])
    (fun n s t => by
      rw [← map_zsmul]
      rw [Prod.smul_mk, smul_zero, Finsupp.smul_single])

lemma beta_apply (f : R →+* S) (s t : S) :
    beta f s t = QuotientAddGroup.mk' (Rel f) (Finsupp.single s t, (0 : S)) := rfl

/-- The inverse of `θ` on the quotient: `tmul f s t ↦ (single s t, 0)`. -/
noncomputable def phi (f : R →+* S) : BalancedTensor f →+ ((S →₀ S) × S) ⧸ Rel f :=
  BalancedTensor.lift f (beta f) (fun s t r => by
    rw [beta_apply f (s * f r) t, beta_apply f s (f r * t)]
    refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
    have hh := Rel_defect_balance f s t r
    simpa [Prod.mk_sub_mk] using hh)

lemma phi_tmul (f : R →+* S) (s t : S) :
    phi f (BalancedTensor.tmul f s t)
      = QuotientAddGroup.mk' (Rel f) (Finsupp.single s t, (0 : S)) := by
  rw [phi, BalancedTensor.lift_tmul, beta_apply]

/-- `phi` is a left inverse of `θ`: the kernel of `θ` is contained in `Rel f`. -/
lemma theta_mem (f : R →+* S) (x : (S →₀ S) × S) (hx : theta f x = 0) : x ∈ Rel f := by
  have h2 : phi f (theta f x) = QuotientAddGroup.mk' (Rel f) x := by
    have hA : ∀ z : S →₀ S, phi f (theta1 f z) = QuotientAddGroup.mk' (Rel f) (inlHom z) := by
      intro z
      rw [theta1_apply]
      rw [map_finsupp_sum (phi f ·) (map_zero (phi f)) (map_add (phi f)) z
        (fun s v => BalancedTensor.tmul f s v)]
      have hsum : z.sum (fun s v => inlHom (Finsupp.single s v)) = inlHom z := by
        rw [← map_finsupp_sum (inlHom ·) (map_zero inlHom) (map_add inlHom) z
          (fun s v => Finsupp.single s v), Finsupp.sum_single]
      rw [← hsum, map_finsupp_sum (QuotientAddGroup.mk' (Rel f) ·)
        (map_zero (QuotientAddGroup.mk' (Rel f))) (map_add (QuotientAddGroup.mk' (Rel f))) z
        (fun s v => inlHom (Finsupp.single s v))]
      exact Finsupp.sum_congr fun s _ => by rw [phi_tmul]; rfl
    have hB : phi f (BalancedTensor.tmul f 1 x.2)
        = QuotientAddGroup.mk' (Rel f) ((0 : S →₀ S), x.2) := by
      rw [phi_tmul]
      refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
      simpa [Prod.mk_sub_mk] using Rel_single_one f x.2
    rw [theta_apply, map_add, hA, hB, ← map_add]
    congr 1
    apply Prod.ext <;> simp [inlHom]
  have h1 : phi f (theta f x) = 0 := by rw [hx, map_zero]
  rw [h2] at h1
  have hker := (QuotientAddGroup.mk' (Rel f)).mem_ker.mpr h1
  rwa [QuotientAddGroup.ker_mk'] at hker

/-- **Mazet's lemma.**  If `∑_s tmul f s (t s) + tmul f 1 ts = 0` in `S ⊗[R] S`, then `t` and
`ts` admit a Mazet presentation: there are finitely many columns `μ`, finitely supported
families `a μ : S →₀ R`, scalars `astar μ ∈ R` and elements `z μ ∈ S` with the stated
relations. -/
theorem syzygy (f : R →+* S) {t : S →₀ S} {ts : S} (h : theta f (t, ts) = 0) :
    ∃ (m : ℕ) (a : Fin m → S →₀ R) (astar : Fin m → R) (z : Fin m → S),
      (∀ μ, (a μ).sum (fun s r => s * f r) + f (astar μ) = 0) ∧
      (∀ s, t s = ∑ μ, f (a μ s) * z μ) ∧
      (ts = ∑ μ, f (astar μ) * z μ) := by
  have hmem : (t, ts) ∈ Rel f := theta_mem f (t, ts) h
  obtain ⟨m, a, astar, z, h1, h2, h3⟩ := hmem
  exact ⟨m, a, astar, z, h1, h2, h3⟩

end MazetU

theorem mazetSyzygyU {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    {t : S →₀ S} {ts : S}
    (h : t.sum (fun s v => Work.ORHughesFree.Epic.BalancedTensor.tmul f s v)
        + Work.ORHughesFree.Epic.BalancedTensor.tmul f 1 ts = 0) :
    ∃ (m : ℕ) (a : Fin m → S →₀ R) (astar : Fin m → R) (z : Fin m → S),
      (∀ μ, (a μ).sum (fun s r => s * f r) + f (astar μ) = 0) ∧
      (∀ s, t s = ∑ μ, f (a μ s) * z μ) ∧
      ts = ∑ μ, f (astar μ) * z μ := by
  have h' : MazetU.theta f (t, ts) = 0 := by
    show MazetU.theta1 f t + BalancedTensor.tmul f 1 ts = 0
    rw [MazetU.theta1_apply]
    exact h
  exact MazetU.syzygy f h'

end Work.Section3.UniverseStenstrom
