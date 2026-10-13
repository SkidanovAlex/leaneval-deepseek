import Mathlib
import Submission.Work.DSM5b.HCF.Surj
import Submission.Work.DSM5b.HCF.SurjTopDefs
import Submission.Work.DSM5b.HCF.perm_eq_zero_of_step
import Submission.Work.DSM5b.HCF.surjIdx_orbit

/-!
# Injectivity of evaluation at the increasing tuple in the top degree of the surjection complex

`Work.DSM5b.HCF.surjD_top_injective`: in the top degree `p+1` (where `p + 2 = ♯S₀`) of the
"surjection complex" `Work.DSM5b.SurjTerm S₀ N` with differential `Work.DSM5b.surjD`, a cocycle is
determined by its value at the increasing enumeration `Work.DSM5b.incTupleE S₀ (p+1) hp`.

In degree `p+1` the cochains are the functions on the bijections `Fin (p+2) → S₀`.  The proof is
the elementary one:

* `surjD_step_of_cocycle`: the cocycle condition, evaluated at the tuple obtained from `σ` by
  re-inserting one of its values, forces `z σ + z (swapEntry σ i) = 0` for every adjacent
  transposition of the entries of `σ` (cocycles are "alternating" in the positions);
* `perm_eq_zero_of_step` (delegated): since the adjacent transpositions generate
  `Equiv.Perm (Fin (p+2))` (`Equiv.Perm.mclosure_swap_castSucc_succ`), this forces `z` to vanish
  on the orbit of `incTupleE`;
* `surjIdx_orbit` (delegated): that orbit is all of `SurjIdx S₀ (p+1)`.

Hence a cocycle with vanishing value at `incTupleE` is zero (`surjD_top_kernel_zero`), and two
cocycles with the same value there coincide.
-/

namespace Work.DSM5b.HCF

open Work.DSM5b

universe u

/-- **The basic step relation of the top-degree cocycle condition.**

`swapEntry σ i` swaps the adjacent entries `i` and `i+1` (positions `i.castSucc` and `i.succ` of
the length-`(p+2)` tuple `σ.1`) of `σ : SurjIdx S₀ (p+1)`.

Put `av := σ.1 i.succ` and `τ : Fin (p+3) → Fin n := Fin.insertNth i.castSucc.castSucc av σ.1`
(inserting `av` at the position of `i`).  Then `tupRng τ = S₀`,
`tupDel i.castSucc.castSucc τ = σ.1` (`Fin.insertNth_comp_succAbove`) and
`tupDel i.succ.succ τ = σ.1 ∘ Equiv.swap i.castSucc i.succ`.  Since `σ.1` is injective
(`tupRng σ.1 = S₀` and `♯S₀ = p+2` is the size of the domain), `av` is the only repeated value of
`τ`, occurring exactly at the two positions `i.castSucc.castSucc` and `i.succ.succ`; hence in the
cocycle condition `surjD (p+1) z τ = 0` only those two summands survive, and they carry the same
sign `(-1)^i`, which is a unit of `R`. -/
theorem surjD_step_of_cocycle {R : Type u} [CommRing R] {n : ℕ} (S₀ : Finset (Fin n))
    (N : Type u) [AddCommGroup N] [Module R N] (p : ℕ) (hp : p + 2 = S₀.card)
    (z : Work.DSM5b.SurjTerm S₀ N (p + 1))
    (hz : Work.DSM5b.surjD (R := R) S₀ N (p + 1) z = 0)
    (σ : Work.DSM5b.SurjIdx S₀ (p + 1)) (i : Fin (p + 1)) :
    z σ + z (swapEntry σ i) = 0 := by
  classical
  have hinj : Function.Injective σ.1 := by
    have h1 : (Finset.univ.image σ.1).card = (Finset.univ : Finset (Fin (p + 2))).card := by
      rw [Finset.card_univ, Fintype.card_fin, ← Work.DSM5b.tupRng, σ.2]
      exact hp.symm
    have h2 : Set.InjOn σ.1 ↑(Finset.univ : Finset (Fin (p + 2))) := Finset.card_image_iff.mp h1
    intro x y hxy
    exact h2 (Finset.mem_univ x) (Finset.mem_univ y) hxy
  set τ : Fin (p + 3) → Fin n := Fin.insertNth (i.castSucc.castSucc) (σ.1 i.succ) σ.1 with hτ
  have hτc : τ ∘ (i.castSucc.castSucc).succAbove = σ.1 := by
    rw [hτ]; exact Fin.insertNth_comp_succAbove _ _ _
  have hτp : τ (i.castSucc.castSucc) = σ.1 i.succ := by
    rw [hτ]; exact Fin.insertNth_apply_same _ _ _
  have hpred : ∀ j : Fin (p + 3), j ≠ i.castSucc.castSucc →
      τ j = σ.1 ((i.castSucc).predAbove j) := by
    intro j hj
    have hh := congrFun hτc ((i.castSucc).predAbove j)
    simp only [Function.comp_apply] at hh
    rwa [Fin.succAbove_predAbove hj] at hh
  have hτrn : Work.DSM5b.tupRng τ = S₀ := by
    have hsub1 : Work.DSM5b.tupRng σ.1 ⊆ Work.DSM5b.tupRng τ := by
      intro x hx
      rw [Work.DSM5b.tupRng, Finset.mem_image] at hx ⊢
      obtain ⟨y, -, rfl⟩ := hx
      exact ⟨(i.castSucc.castSucc).succAbove y, Finset.mem_univ _, congrFun hτc y⟩
    have hsub2 : Work.DSM5b.tupRng τ ⊆ Work.DSM5b.tupRng σ.1 := by
      intro x hx
      rw [Work.DSM5b.tupRng, Finset.mem_image] at hx ⊢
      obtain ⟨j, -, rfl⟩ := hx
      by_cases hj : j = i.castSucc.castSucc
      · exact ⟨i.succ, Finset.mem_univ _, by rw [hj, hτp]⟩
      · exact ⟨(i.castSucc).predAbove j, Finset.mem_univ _, by rw [hpred j hj]⟩
    exact (Finset.Subset.antisymm hsub2 hsub1).trans σ.2
  have hdel1 : Work.DSM5b.tupDel (i.castSucc.castSucc) τ = σ.1 := by
    funext x
    rw [Work.DSM5b.tupDel_apply]
    exact congrFun hτc x
  have hdel2 : Work.DSM5b.tupDel (i.succ.succ) τ
      = σ.1 ∘ Equiv.swap (i.castSucc) (i.succ) := by
    funext x
    rw [Work.DSM5b.tupDel_apply, Function.comp_apply]
    rcases lt_trichotomy (x : ℕ) (i : ℕ) with hlt | heq | hgt
    · have hxa : x ≠ i.castSucc := by
        intro h; rw [h] at hlt; simp only [Fin.val_castSucc] at hlt; omega
      have hxb : x ≠ i.succ := by
        intro h; rw [h] at hlt; simp only [Fin.val_succ] at hlt; omega
      rw [Equiv.swap_apply_def, if_neg hxa, if_neg hxb]
      have hs : (i.succ.succ : Fin (p + 3)).succAbove x = x.castSucc :=
        Fin.succAbove_succ_of_le i.succ x (by rw [Fin.le_def]; simp only [Fin.val_succ]; omega)
      have hs2 : (i.castSucc.castSucc : Fin (p + 3)).succAbove x = x.castSucc :=
        Fin.succAbove_castSucc_of_lt (i.castSucc) x (by rw [Fin.lt_def, Fin.val_castSucc]; exact hlt)
      rw [hs, ← hs2]
      exact congrFun hτc x
    · have hxa : x = i.castSucc := Fin.ext heq
      rw [hxa, Equiv.swap_apply_left]
      have hs : (i.succ.succ : Fin (p + 3)).succAbove (i.castSucc) = i.castSucc.castSucc :=
        Fin.succAbove_succ_of_le i.succ (i.castSucc)
          (by rw [Fin.le_def]; simp only [Fin.val_succ]; omega)
      rw [hs, hτp]
    · by_cases hxb : x = i.succ
      · rw [hxb, Equiv.swap_apply_right]
        have hs : (i.succ.succ : Fin (p + 3)).succAbove (i.succ) = (i.castSucc).succ := by
          rw [Fin.succAbove_succ_of_le (i.succ) (i.succ) le_rfl]
          exact Fin.ext rfl
        have hs2 : (i.castSucc.castSucc : Fin (p + 3)).succAbove (i.castSucc) = (i.castSucc).succ :=
          Fin.succAbove_castSucc_of_le (i.castSucc) (i.castSucc) le_rfl
        rw [hs, ← hs2]
        exact congrFun hτc (i.castSucc)
      · have hxne : (x : ℕ) ≠ (i : ℕ) + 1 := by
          intro h
          exact hxb (Fin.ext (by simp only [Fin.val_succ]; exact h))
        have hxlt : (i.succ : Fin (p + 2)) < x := by
          rw [Fin.lt_def]; simp only [Fin.val_succ]; omega
        have hxa : x ≠ i.castSucc := by
          intro h; rw [h] at hgt; exact absurd hgt (lt_irrefl _)
        rw [Equiv.swap_apply_def, if_neg hxa, if_neg hxb]
        have hs : (i.succ.succ : Fin (p + 3)).succAbove x = x.succ :=
          Fin.succAbove_succ_of_lt i.succ x hxlt
        have hs2 : (i.castSucc.castSucc : Fin (p + 3)).succAbove x = x.succ :=
          Fin.succAbove_castSucc_of_le (i.castSucc) x
            (by rw [Fin.le_def]; simp only [Fin.val_castSucc]; omega)
        rw [hs, ← hs2]
        exact congrFun hτc x
  have hsurj : ∀ j : Fin (p + 3), Work.DSM5b.tupRng (Work.DSM5b.tupDel j τ) = S₀ →
      j = i.castSucc.castSucc ∨ j = i.succ.succ := by
    intro j hj
    have hmem : τ j ∈ Work.DSM5b.tupRng (Work.DSM5b.tupDel j τ) := by
      rw [hj, ← hτrn, Work.DSM5b.tupRng, Finset.mem_image]
      exact ⟨j, Finset.mem_univ _, rfl⟩
    rw [Work.DSM5b.tupRng, Finset.mem_image] at hmem
    obtain ⟨b, -, hb⟩ := hmem
    have hb' : τ (j.succAbove b) = τ j := hb
    have hnj : j.succAbove b ≠ j := Fin.succAbove_ne j b
    by_cases hj1 : j = i.castSucc.castSucc
    · exact Or.inl hj1
    · right
      by_cases hm1 : j.succAbove b = i.castSucc.castSucc
      · have hτm : τ (j.succAbove b) = σ.1 i.succ := by rw [hm1, hτp]
        have hτj : τ j = σ.1 ((i.castSucc).predAbove j) := hpred j hj1
        rw [hτm, hτj] at hb'
        have hpe : (i.castSucc).predAbove j = i.succ := (hinj hb').symm
        have hjj : j = (i.castSucc.castSucc).succAbove ((i.castSucc).predAbove j) :=
          (Fin.succAbove_predAbove hj1).symm
        rw [hjj, hpe]
        exact Fin.succAbove_castSucc_of_le (i.castSucc) (i.succ) (Fin.castSucc_le_succ i)
      · exfalso
        have hτm : τ (j.succAbove b) = σ.1 ((i.castSucc).predAbove (j.succAbove b)) :=
          hpred _ hm1
        have hτj : τ j = σ.1 ((i.castSucc).predAbove j) := hpred j hj1
        rw [hτm, hτj] at hb'
        have hpe : (i.castSucc).predAbove (j.succAbove b) = (i.castSucc).predAbove j := hinj hb'
        have h1 : (i.castSucc.castSucc).succAbove ((i.castSucc).predAbove j) = j :=
          Fin.succAbove_predAbove hj1
        have h2 : (i.castSucc.castSucc).succAbove ((i.castSucc).predAbove (j.succAbove b))
            = j.succAbove b := Fin.succAbove_predAbove hm1
        exact hnj (by rw [← h2, hpe, h1])
  have hcyc : (∑ j : Fin (p + 3), (if h : Work.DSM5b.tupRng (Work.DSM5b.tupDel j τ) = S₀ then
      ((-1 : R) ^ (j : ℕ)) • z ⟨Work.DSM5b.tupDel j τ, h⟩ else 0)) = 0 := by
    have h0 := congrFun hz ⟨τ, hτrn⟩
    rw [Pi.zero_apply] at h0
    exact h0
  have hf_pins : (if h : Work.DSM5b.tupRng (Work.DSM5b.tupDel (i.castSucc.castSucc) τ) = S₀ then
        ((-1 : R) ^ (((i.castSucc.castSucc : Fin (p + 3)) : ℕ))) •
          z ⟨Work.DSM5b.tupDel (i.castSucc.castSucc) τ, h⟩ else 0)
      = ((-1 : R) ^ (((i.castSucc.castSucc : Fin (p + 3)) : ℕ))) • z σ := by
    have hR : Work.DSM5b.tupRng (Work.DSM5b.tupDel (i.castSucc.castSucc) τ) = S₀ := by
      rw [hdel1]; exact σ.2
    rw [dif_pos hR]
    rw [show (⟨Work.DSM5b.tupDel (i.castSucc.castSucc) τ, hR⟩ : Work.DSM5b.SurjIdx S₀ (p + 1))
        = σ from Subtype.ext hdel1]
  have hf_q : (if h : Work.DSM5b.tupRng (Work.DSM5b.tupDel (i.succ.succ) τ) = S₀ then
        ((-1 : R) ^ (((i.succ.succ : Fin (p + 3)) : ℕ))) •
          z ⟨Work.DSM5b.tupDel (i.succ.succ) τ, h⟩ else 0)
      = ((-1 : R) ^ (((i.succ.succ : Fin (p + 3)) : ℕ))) • z (swapEntry σ i) := by
    have hR : Work.DSM5b.tupRng (Work.DSM5b.tupDel (i.succ.succ) τ) = S₀ := by
      rw [hdel2]
      exact (tupRng_comp_perm (m := p + 1) (Equiv.swap (i.castSucc) (i.succ)) σ.1).trans σ.2
    rw [dif_pos hR]
    rw [show (⟨Work.DSM5b.tupDel (i.succ.succ) τ, hR⟩ : Work.DSM5b.SurjIdx S₀ (p + 1))
        = swapEntry σ i from Subtype.ext hdel2]
  have hpq : (i.castSucc.castSucc : Fin (p + 3)) ≠ (i.succ.succ : Fin (p + 3)) := by
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hh
    omega
  have hsum : (∑ j : Fin (p + 3), (if h : Work.DSM5b.tupRng (Work.DSM5b.tupDel j τ) = S₀ then
        ((-1 : R) ^ (j : ℕ)) • z ⟨Work.DSM5b.tupDel j τ, h⟩ else 0))
      = ((-1 : R) ^ (((i.castSucc.castSucc : Fin (p + 3)) : ℕ))) • z σ
        + ((-1 : R) ^ (((i.succ.succ : Fin (p + 3)) : ℕ))) • z (swapEntry σ i) := by
    have h1 : (∑ j ∈ ({(i.castSucc.castSucc : Fin (p + 3)),
          (i.succ.succ : Fin (p + 3))} : Finset (Fin (p + 3))),
        (if h : Work.DSM5b.tupRng (Work.DSM5b.tupDel j τ) = S₀ then
          ((-1 : R) ^ (j : ℕ)) • z ⟨Work.DSM5b.tupDel j τ, h⟩ else 0))
        = (∑ j : Fin (p + 3), (if h : Work.DSM5b.tupRng (Work.DSM5b.tupDel j τ) = S₀ then
          ((-1 : R) ^ (j : ℕ)) • z ⟨Work.DSM5b.tupDel j τ, h⟩ else 0)) := by
      refine Finset.sum_subset (by intro x _; exact Finset.mem_univ x) ?_
      intro x _ hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      have hnc : ¬ (Work.DSM5b.tupRng (Work.DSM5b.tupDel x τ) = S₀) := by
        intro hcon
        rcases hsurj x hcon with h | h
        · exact hx (Or.inl h)
        · exact hx (Or.inr h)
      rw [dif_neg hnc]
    have h2 : (∑ j ∈ ({(i.castSucc.castSucc : Fin (p + 3)),
          (i.succ.succ : Fin (p + 3))} : Finset (Fin (p + 3))),
        (if h : Work.DSM5b.tupRng (Work.DSM5b.tupDel j τ) = S₀ then
          ((-1 : R) ^ (j : ℕ)) • z ⟨Work.DSM5b.tupDel j τ, h⟩ else 0))
        = ((-1 : R) ^ (((i.castSucc.castSucc : Fin (p + 3)) : ℕ))) • z σ
          + ((-1 : R) ^ (((i.succ.succ : Fin (p + 3)) : ℕ))) • z (swapEntry σ i) := by
      rw [Finset.sum_pair hpq]
      rw [hf_pins, hf_q]
    rw [← h1, h2]
  have hsign : ((-1 : R) ^ (((i.succ.succ : Fin (p + 3)) : ℕ)))
      = ((-1 : R) ^ (((i.castSucc.castSucc : Fin (p + 3)) : ℕ))) := by
    have hv : (((i.succ.succ : Fin (p + 3)) : ℕ))
        = (((i.castSucc.castSucc : Fin (p + 3)) : ℕ)) + 2 := by
      simp only [Fin.val_castSucc, Fin.val_succ, Nat.add_assoc]
    rw [hv, pow_add, show (-1 : R) ^ 2 = 1 by norm_num, mul_one]
  have hfinal : ((-1 : R) ^ (((i.castSucc.castSucc : Fin (p + 3)) : ℕ)))
      • (z σ + z (swapEntry σ i)) = 0 := by
    rw [hsign] at hsum
    have hz' : ((-1 : R) ^ (((i.castSucc.castSucc : Fin (p + 3)) : ℕ))) • z σ
        + ((-1 : R) ^ (((i.castSucc.castSucc : Fin (p + 3)) : ℕ))) • z (swapEntry σ i) = 0 :=
      hsum.symm.trans hcyc
    rwa [← smul_add] at hz'
  have hcc : ((-1 : R) ^ (((i.castSucc.castSucc : Fin (p + 3)) : ℕ)))
      * ((-1 : R) ^ (((i.castSucc.castSucc : Fin (p + 3)) : ℕ))) = 1 := by
    rw [← pow_add]
    rw [show (((i.castSucc.castSucc : Fin (p + 3)) : ℕ))
        + (((i.castSucc.castSucc : Fin (p + 3)) : ℕ))
        = 2 * (((i.castSucc.castSucc : Fin (p + 3)) : ℕ)) from by omega]
    rw [pow_mul, show (-1 : R) ^ 2 = 1 by norm_num, one_pow]
  calc z σ + z (swapEntry σ i)
      = (1 : R) • (z σ + z (swapEntry σ i)) := (one_smul _ _).symm
    _ = (((-1 : R) ^ (((i.castSucc.castSucc : Fin (p + 3)) : ℕ)))
          * ((-1 : R) ^ (((i.castSucc.castSucc : Fin (p + 3)) : ℕ))))
          • (z σ + z (swapEntry σ i)) := by rw [hcc]
    _ = ((-1 : R) ^ (((i.castSucc.castSucc : Fin (p + 3)) : ℕ)))
          • (((-1 : R) ^ (((i.castSucc.castSucc : Fin (p + 3)) : ℕ)))
          • (z σ + z (swapEntry σ i))) := by rw [mul_smul]
    _ = ((-1 : R) ^ (((i.castSucc.castSucc : Fin (p + 3)) : ℕ))) • 0 := by rw [hfinal]
    _ = 0 := smul_zero _

/-- **A cocycle in the top degree with vanishing value at the increasing tuple is zero.**

This is the linear form of `surjD_top_injective`. -/
theorem surjD_top_kernel_zero {R : Type u} [CommRing R] {n : ℕ} (S₀ : Finset (Fin n)) (N : Type u)
    [AddCommGroup N] [Module R N] (p : ℕ) (hp : p + 2 = S₀.card)
    (z : Work.DSM5b.SurjTerm S₀ N (p + 1))
    (hz : Work.DSM5b.surjD (R := R) S₀ N (p + 1) z = 0)
    (he : z (Work.DSM5b.incTupleE S₀ (p + 1) hp) = 0) :
    z = 0 := by
  classical
  set e := Work.DSM5b.incTupleE S₀ (p + 1) hp with he_def
  set φ : Equiv.Perm (Fin (p + 2)) → Work.DSM5b.SurjIdx S₀ (p + 1) :=
    fun π => ⟨e.1 ∘ π.1, (tupRng_comp_perm (m := p + 1) π e.1).trans e.2⟩ with hφ_def
  set F : Equiv.Perm (Fin (p + 2)) → N := fun π => z (φ π) with hF_def
  have hF1 : F 1 = 0 := by
    have hφ1 : φ 1 = e := Subtype.ext (by funext x; rfl)
    simp only [hF_def]
    rw [hφ1]
    exact he
  have hstep : ∀ (π : Equiv.Perm (Fin (p + 2))) (i : Fin (p + 1)),
      F (π * Equiv.swap i.castSucc i.succ) = - F π := by
    intro π i
    have hswap : φ (π * Equiv.swap i.castSucc i.succ) = swapEntry (φ π) i := by
      apply Subtype.ext
      simp only [swapEntry_val]
      rw [hφ_def]
      simp only
      ext x
      simp [Equiv.Perm.mul_apply]
    have hs := surjD_step_of_cocycle S₀ N p hp z hz (φ π) i
    simp only [hF_def]
    rw [← hswap] at hs
    exact eq_neg_of_add_eq_zero_right hs
  funext σ
  obtain ⟨π, hπ⟩ := surjIdx_orbit S₀ p hp σ
  have hσ : σ = φ π := Subtype.ext hπ
  have hz0 : F π = 0 := perm_eq_zero_of_step F hF1 hstep π
  rw [hF_def] at hz0
  rw [hσ]
  exact hz0

theorem surjD_top_injective {R : Type u} [CommRing R] {n : ℕ} (S₀ : Finset (Fin n)) (N : Type u)
    [AddCommGroup N] [Module R N] (p : ℕ) (hp : p + 2 = S₀.card)
    (z z' : Work.DSM5b.SurjTerm S₀ N (p + 1))
    (hz : Work.DSM5b.surjD (R := R) S₀ N (p + 1) z = 0)
    (hz' : Work.DSM5b.surjD (R := R) S₀ N (p + 1) z' = 0)
    (h : z (Work.DSM5b.incTupleE S₀ (p + 1) hp) = z' (Work.DSM5b.incTupleE S₀ (p + 1) hp)) :
    z = z' := by
  have hw : (z - z') = 0 := by
    apply surjD_top_kernel_zero (R := R) S₀ N p hp
    · rw [map_sub, hz, hz', sub_zero]
    · simp only [Pi.sub_apply]
      rw [h, sub_self]
  exact sub_eq_zero.mp hw

end Work.DSM5b.HCF
