/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The Magnus step for a root, exponent-sum-zero case

This file proves `Work.OROneRel.magnus_step_root_eps_zero`: the exponent-sum-zero case of the
Magnus--Moldavanskii step with the root tracked up to conjugacy.

Setting: `u : FreeGroup α` is cyclically reduced, not a proper power, `t : α` occurs in `u` with
exponent sum zero and `l ≥ 1`.  Then `⟨α | u ^ l⟩` is an HNN extension of the shorter one-relator
group `⟨β | v ^ l⟩` (same exponent `l`), where `v` is the Magnus rewriting of `u` with respect to
`t`, and the class of `u` is conjugate to the class of `v`.

The proof runs the exponent-sum-zero Magnus--Moldavanskii step (`mmStepData_of_expsum_zero`) at the
*power* relator `u ^ l` and then transports the resulting HNN structure back to the root: the
decorated alphabet of `u ^ l` agrees with that of `u`, and the Magnus rewriting of `u ^ l` is the
`l`-th power of the rewriting of `u`.
-/
import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.freiheitssatz_at
import Submission.Work.OROneRel.rho_magnet
import Submission.Work.OROneRel.rho_injective
import Submission.Work.OROneRel.magnusMap_injective_range
import Submission.Work.OROneRel.ne_one_of_not_isProperPower
import Submission.Work.OROneRel.isCyclicallyReducedRelator_pow
import Submission.Work.OROneRel.relatorNorm_pow_of_isCyclicallyReduced

namespace Work.OROneRel.EpsV2

universe u

variable {α : Type u}

/-! ## 0. Elementary word combinatorics of the Magnus rewriting

These are the few facts about `wordEps` and `magRew` that are needed below; they are local copies
(in the `Work.OROneRel.EpsV2` namespace) of the corresponding lemmas of
`Submission.Work.OROneRel.magnus_step_root`, so that this file does not depend on that module. -/

/-- The exponent sum of the empty word is `0`. -/
theorem wordEps_nil (t : α) : wordEps t ([] : List (α × Bool)) = 0 := by
  classical
  simp [wordEps]

/-- The exponent sum of a one-letter word is the signed contribution of that letter. -/
theorem wordEps_singleton [DecidableEq α] (t : α) (p : α × Bool) :
    wordEps t [p] = if p.1 = t then (if p.2 then (1 : ℤ) else -1) else 0 := by
  classical
  simp [wordEps]

/-- The exponent sum of a concatenation is the sum of the exponent sums. -/
theorem wordEps_append [DecidableEq α] (t : α) (L₁ L₂ : List (α × Bool)) :
    wordEps t (L₁ ++ L₂) = wordEps t L₁ + wordEps t L₂ := by
  classical
  simp [wordEps, List.map_append, List.sum_append]

/-- The exponent sum of a word, read off from the first letter. -/
theorem wordEps_cons [DecidableEq α] (t : α) (p : α × Bool) (L : List (α × Bool)) :
    wordEps t (p :: L) = (if p.1 = t then (if p.2 then (1 : ℤ) else -1) else 0) + wordEps t L := by
  rw [← List.singleton_append, wordEps_append, wordEps_singleton]

/-- The Magnus rewriting of the empty word is empty. -/
theorem magRew_nil (t : α) (acc : ℤ) : magRew t acc ([] : List (α × Bool)) = [] := by
  classical
  simp only [magRew]

/-- The Magnus rewriting, read off from the first letter. -/
theorem magRew_cons [DecidableEq α] (t : α) (acc : ℤ) (p : α × Bool) (L : List (α × Bool)) :
    magRew t acc (p :: L)
      = if h : p.1 = t then magRew t (acc + (if p.2 then (1 : ℤ) else -1)) L
        else ((⟨p.1, h⟩, acc), p.2) :: magRew t acc L := by
  classical
  simp only [magRew]
  split <;> rfl

/-- The Magnus rewriting is compatible with concatenation. -/
theorem magRew_append [DecidableEq α] (t : α) (L₁ L₂ : List (α × Bool)) (acc : ℤ) :
    magRew t acc (L₁ ++ L₂) = magRew t acc L₁ ++ magRew t (acc + wordEps t L₁) L₂ := by
  induction L₁ generalizing acc with
  | nil => simp [magRew_nil, wordEps_nil]
  | cons p L ih =>
    by_cases h : p.1 = t
    · have hδ : wordEps t (p :: L) = (if p.2 then (1 : ℤ) else -1) + wordEps t L := by
        rw [wordEps_cons, if_pos h]
      rw [List.cons_append, hδ, magRew_cons t acc p (L ++ L₂), dif_pos h,
        magRew_cons t acc p L, dif_pos h, ih (acc + (if p.2 then (1 : ℤ) else -1)),
        show acc + ((if p.2 then (1 : ℤ) else -1) + wordEps t L)
          = (acc + (if p.2 then (1 : ℤ) else -1)) + wordEps t L from by ring]
    · have hδ : wordEps t (p :: L) = 0 + wordEps t L := by
        rw [wordEps_cons, if_neg h]
      rw [List.cons_append, hδ, magRew_cons t acc p (L ++ L₂), dif_neg h,
        magRew_cons t acc p L, dif_neg h, ih acc, List.cons_append,
        show acc + (0 + wordEps t L) = acc + wordEps t L from by ring]

/-- `(L.replicate (n+1)).flatten = L ++ (L.replicate n).flatten`. -/
theorem flatten_replicate_succ {β : Type*} (L : List β) (n : ℕ) :
    (List.replicate (n + 1) L).flatten = L ++ (List.replicate n L).flatten := by
  rw [List.replicate_succ, List.flatten_cons]

/-- If the exponent sum of `t` in `L` vanishes, the Magnus rewriting of a repetition of `L` is the
corresponding repetition of the rewriting. -/
theorem magRew_flatten_replicate_of_wordEps_eq_zero [DecidableEq α] (t : α) (acc : ℤ)
    (L : List (α × Bool)) (hL : wordEps t L = 0) (n : ℕ) :
    magRew t acc (List.replicate n L).flatten
      = (List.replicate n (magRew t acc L)).flatten := by
  induction n generalizing acc with
  | zero => simp [magRew_nil]
  | succ n ih =>
    have hacc : acc + wordEps t L = acc := by rw [hL, add_zero]
    rw [flatten_replicate_succ, flatten_replicate_succ, magRew_append, hacc, ih]

/-! ## 1. The Magnus rewriting of a power -/

/-- The Magnus rewriting of a power of a cyclically reduced word of exponent sum zero in `t` is the
concatenation of the copies of the rewriting. -/
theorem mmList_pow (t : α) (u : FreeGroup α) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (l : ℕ) :
    mmList t (u ^ l) = (List.replicate l (mmList t u)).flatten := by
  classical
  have hh : FreeGroup.IsCyclicallyReduced (FreeGroup.toWord u) := by
    simpa only [IsCyclicallyReducedRelator] using hu
  have hred : FreeGroup.IsReduced (List.flatten (List.replicate l (FreeGroup.toWord u))) :=
    (hh.flatten_replicate l).1
  have hword : FreeGroup.toWord (u ^ l)
      = List.flatten (List.replicate l (FreeGroup.toWord u)) := by
    rw [FreeGroup.toWord_pow, hred.reduce_eq]
  have hw : wordEps t u.toWord = 0 := he
  rw [mmList, mmList, hword,
    magRew_flatten_replicate_of_wordEps_eq_zero t 0 u.toWord hw l,
    magRew_zero_eq_rewrite]

/-- The decorations of a generator `x ≠ t` occurring in the rewriting of `u ^ l` are the same as
those occurring in the rewriting of `u`. -/
theorem mmDecs_pow (t : α) (u : FreeGroup α) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (l : ℕ) (hl : 1 ≤ l) (x : {x : α // x ≠ t}) :
    mmDecs t (u ^ l) x = mmDecs t u x := by
  classical
  ext k
  rw [mem_mmDecs_iff, mem_mmDecs_iff, mmList_pow t u hu he l]
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨L', hL', hb'⟩ := List.mem_flatten.mp hb
    rw [List.eq_of_mem_replicate hL'] at hb'
    exact ⟨b, hb'⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, List.mem_flatten.mpr
      ⟨mmList t u, List.mem_replicate.mpr ⟨by omega, rfl⟩, hb⟩⟩

theorem mmLo_pow (t : α) (u : FreeGroup α) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (l : ℕ) (hl : 1 ≤ l) (x : {x : α // x ≠ t}) :
    mmLo t (u ^ l) x = mmLo t u x := by
  classical
  rw [mmLo, mmLo, mmDecs_pow t u hu he l hl x]

theorem mmHi_pow (t : α) (u : FreeGroup α) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (l : ℕ) (hl : 1 ≤ l) (x : {x : α // x ≠ t}) :
    mmHi t (u ^ l) x = mmHi t u x := by
  classical
  rw [mmHi, mmHi, mmDecs_pow t u hu he l hl x]

/-- The interval closure of the decorations is the same for `u` and `u ^ l`. -/
theorem mmDecSet_pow (t : α) (u : FreeGroup α) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (l : ℕ) (hl : 1 ≤ l) :
    mmDecSet t (u ^ l) = mmDecSet t u := by
  ext p
  simp only [mmDecSet, Set.mem_ofPred_eq]
  rw [mmLo_pow t u hu he l hl p.1, mmHi_pow t u hu he l hl p.1]

/-! ## 2. The decorated alphabet of `u ^ l` and the root -/

/-- The transport of the decorated alphabet from `u` to `u ^ l` (the underlying decorated letters are
unchanged). -/
noncomputable def mmTransFun (t : α) (u : FreeGroup α) (l : ℕ)
    (hu : IsCyclicallyReducedRelator u) (he : eps t u = 0) (hl : 1 ≤ l) :
    mmBeta t u → mmBeta t (u ^ l) :=
  fun e => ⟨e.1, (mmDecSet_pow t u hu he l hl).symm ▸ e.2⟩

/-- The Magnus rewriting of `u` with respect to `t`, viewed in the decorated alphabet of `u ^ l`. -/
noncomputable def rootW (t : α) (u : FreeGroup α) (l : ℕ) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (hl : 1 ≤ l) : FreeGroup (mmBeta t (u ^ l)) :=
  FreeGroup.map (mmTransFun t u l hu he hl) (mmW t u)

theorem mmTransFun_val (t : α) (u : FreeGroup α) (l : ℕ) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (hl : 1 ≤ l) (e : mmBeta t u) :
    ((mmTransFun t u l hu he hl e : mmBeta t (u ^ l)) : MMAlpha t) = (e : MMAlpha t) := rfl

/-- `rootW` as a word in the decorated alphabet. -/
theorem rootW_eq (t : α) (u : FreeGroup α) (l : ℕ) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (hl : 1 ≤ l) :
    rootW t u l hu he hl =
      FreeGroup.mk ((mmWL t u).map (fun q => (mmTransFun t u l hu he hl q.1, q.2))) := by
  rw [rootW, mmW, FreeGroup.map.mk]

/-- `FreeGroup.mk` of a repetition of a word is the corresponding power. -/
theorem mk_flatten_rep {β : Type*} (L : List (β × Bool)) (l : ℕ) :
    FreeGroup.mk ((List.replicate l L).flatten) = (FreeGroup.mk L) ^ l := by
  induction l with
  | zero => rw [List.replicate_zero, List.flatten_nil, pow_zero]; rfl
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, rho_mk_append, ih, pow_succ']

/-- The Magnus rewriting of `u ^ l` is the concatenation of the copies of the rewriting of `u`,
transported to the decorated alphabet of `u ^ l`. -/
theorem mmWL_pow_trans (t : α) (u : FreeGroup α) (l : ℕ) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (hl : 1 ≤ l) :
    mmWL t (u ^ l) =
      (List.replicate l ((mmWL t u).map (fun q => (mmTransFun t u l hu he hl q.1, q.2)))).flatten := by
  classical
  have hinner : (mmList t u).map (fun p => (mmBetaOf t (u ^ l) p.1, p.2))
      = (mmWL t u).map (fun q => (mmTransFun t u l hu he hl q.1, q.2)) := by
    rw [show mmWL t u = (mmList t u).map (fun p => (mmBetaOf t u p.1, p.2)) from by rw [mmWL]]
    rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    have hpm : p.1 ∈ mmDecSet t u := mmList_mem_decSet t u hp
    have hpm' : p.1 ∈ mmDecSet t (u ^ l) := (mmDecSet_pow t u hu he l hl).symm ▸ hpm
    simp only [Function.comp_apply]
    refine Prod.ext ?_ rfl
    refine Subtype.ext ?_
    rw [mmBetaOf_val t (u ^ l) hpm', mmTransFun_val, mmBetaOf_val t u hpm]
  calc mmWL t (u ^ l)
      = (mmList t (u ^ l)).map (fun p => (mmBetaOf t (u ^ l) p.1, p.2)) := by rw [mmWL]
    _ = (((List.replicate l (mmList t u)).flatten).map
            (fun p => (mmBetaOf t (u ^ l) p.1, p.2))) := by rw [mmList_pow t u hu he l]
    _ = ((List.replicate l (mmList t u)).map
            (List.map (fun p => (mmBetaOf t (u ^ l) p.1, p.2)))).flatten := by rw [List.map_flatten]
    _ = (List.replicate l ((mmList t u).map
            (fun p => (mmBetaOf t (u ^ l) p.1, p.2)))).flatten := by rw [List.map_replicate]
    _ = (List.replicate l ((mmWL t u).map
            (fun q => (mmTransFun t u l hu he hl q.1, q.2)))).flatten := by rw [hinner]

/-- **The `l`-th power of the root is the Magnus rewriting of `u ^ l`.** -/
theorem rootW_pow (t : α) (u : FreeGroup α) (l : ℕ) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (hl : 1 ≤ l) :
    rootW t u l hu he hl ^ l = mmW t (u ^ l) := by
  rw [rootW_eq, ← mk_flatten_rep ((mmWL t u).map
      (fun q => (mmTransFun t u l hu he hl q.1, q.2))) l, mmW, mmWL_pow_trans t u l hu he hl]

/-! ## 3. The root is again not a proper power and is shorter -/

/-- The expansion of a decorated letter `(x,k)`: the conjugate `t ^ k * x * t ^ (-k)`. -/
noncomputable def mmRhoFun (t : α) (p : MMAlpha t) : FreeGroup α :=
  FreeGroup.of t ^ p.2 * FreeGroup.of (p.1 : α) * FreeGroup.of t ^ (-p.2)

/-- `FreeGroup.lift` commutes with `FreeGroup.map`. -/
theorem lift_comp_map {γ δ M : Type*} [Group M] (f : δ → M) (g : γ → δ) :
    (FreeGroup.lift f).comp (FreeGroup.map g) = FreeGroup.lift (fun a => f (g a)) := by
  refine FreeGroup.ext_hom _ _ fun a => ?_
  rw [MonoidHom.comp_apply, FreeGroup.map.of, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]

/-- The value of `lift_comp_map` on an element. -/
theorem lift_map_apply {γ δ M : Type*} [Group M] (f : δ → M) (g : γ → δ) (w : FreeGroup γ) :
    FreeGroup.lift f (FreeGroup.map g w) = FreeGroup.lift (fun a => f (g a)) w :=
  congrArg (fun φ : FreeGroup γ →* M => φ w) (lift_comp_map f g)

/-- The expansion of the Magnus rewriting of `u` is `u` itself. -/
theorem lift_mmRho_mmW (t : α) (u : FreeGroup α) (he : eps t u = 0) :
    FreeGroup.lift (fun p : mmBeta t u => mmRhoFun t p.1) (mmW t u) = u := by
  classical
  have hcomp : FreeGroup.lift (fun p : mmBeta t u => mmRhoFun t p.1)
      = (rho t).comp (FreeGroup.map (fun p : mmBeta t u => (p.1 : MMAlpha t))) := by
    refine FreeGroup.ext_hom _ _ fun p => ?_
    rw [MonoidHom.comp_apply, FreeGroup.map.of, FreeGroup.lift_apply_of]
    rw [rho, FreeGroup.lift_apply_of]
    rfl
  rw [hcomp, MonoidHom.comp_apply, mmW_map_val]
  rw [show FreeGroup.mk (mmList t u) = magnet u t from rfl]
  exact rho_magnet u t he

/-- The expansion of the root `rootW` is `u`. -/
theorem lift_mmRho_rootW (t : α) (u : FreeGroup α) (l : ℕ) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (hl : 1 ≤ l) :
    FreeGroup.lift (fun p : mmBeta t (u ^ l) => mmRhoFun t p.1) (rootW t u l hu he hl) = u := by
  rw [rootW, lift_map_apply]
  have : (fun p : mmBeta t u =>
        mmRhoFun t ((mmTransFun t u l hu he hl p : mmBeta t (u ^ l)) : MMAlpha t))
      = (fun p : mmBeta t u => mmRhoFun t (p : MMAlpha t)) := by
    funext p
    rw [mmTransFun_val]
  rw [this]
  exact lift_mmRho_mmW t u he

/-- The root is not a proper power. -/
theorem not_isProperPower_rootW (t : α) (u : FreeGroup α) (l : ℕ)
    (hu : ¬ IsProperPower u) (hcyc : IsCyclicallyReducedRelator u) (he : eps t u = 0)
    (hl : 1 ≤ l) : ¬ IsProperPower (rootW t u l hcyc he hl) := by
  classical
  rintro ⟨z, k, hk, hzk⟩
  have h := lift_mmRho_rootW t u l hcyc he hl
  rw [hzk, map_pow] at h
  exact hu ⟨FreeGroup.lift (fun p : mmBeta t (u ^ l) => mmRhoFun t p.1) z, k, hk, h.symm⟩

/-- The root is strictly shorter than `u`. -/
theorem relatorNorm_rootW_lt (t : α) (u : FreeGroup α) (l : ℕ) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (hl : 1 ≤ l) (ht : t ∈ relatorLetters u) :
    relatorNorm (rootW t u l hu he hl) < relatorNorm u := by
  classical
  have h1 : relatorNorm (rootW t u l hu he hl) ≤ (mmList t u).length := by
    rw [rootW_eq]
    refine le_trans FreeGroup.norm_mk_le ?_
    rw [List.length_map, show (mmWL t u).length = (mmList t u).length from by rw [mmWL, List.length_map]]
  have h2 : (mmList t u).length = (rewrite t u.toWord).length := by
    rw [mmList, magRew_zero_eq_rewrite]
  have h3 : (rewrite t u.toWord).length < u.toWord.length := by
    obtain ⟨b, hb⟩ : ∃ b : Bool, (t, b) ∈ u.toWord := ht
    cases b
    · exact rewrite_length_lt t (L := u.toWord) (Or.inr hb)
    · exact rewrite_length_lt t (L := u.toWord) (Or.inl hb)
  have h4 : u.toWord.length = relatorNorm u := rfl
  omega

/-! ## 4. The tracking of the root through the HNN step -/

section Tracking

variable {t : α} {r : FreeGroup α}

/-- The image of the Magnus rewriting in the HNN extension: it is the base element itself. -/
theorem mmTheta_lift_mmRho (hFw : FreiheitssatzAt (mmW t r))
    (hc : IsCyclicallyReducedRelator (mmW t r))
    (hA : (mmW t r) ∉ Subgroup.closure (FreeGroup.of '' mmTA t r))
    (hB : (mmW t r) ∉ Subgroup.closure (FreeGroup.of '' mmTB t r))
    (w : FreeGroup (mmBeta t r)) :
    (FreeGroup.lift (mmThetaFun hFw hc hA hB))
        (FreeGroup.lift (fun p : mmBeta t r => mmRhoFun t p.1) w)
      = HNNExtension.of (PresentedGroup.mk ({mmW t r} : Set (FreeGroup (mmBeta t r))) w) := by
  have hcomp : (FreeGroup.lift (mmThetaFun hFw hc hA hB)).comp
        (FreeGroup.lift (fun p : mmBeta t r => mmRhoFun t p.1))
      = (HNNExtension.of).comp (PresentedGroup.mk ({mmW t r} : Set (FreeGroup (mmBeta t r)))) := by
    refine FreeGroup.ext_hom _ _ fun e => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    set k : ℤ := (e : MMAlpha t).2 with hk
    set x : {a : α // a ≠ t} := (e : MMAlpha t).1 with hx
    have hkdec : ((x, k) : MMAlpha t) ∈ mmDecSet t r := e.2
    have hkx : mmLo t r x ≤ k := by simpa using hkdec.1
    have hkx2 : k ≤ mmHi t r x := by simpa using hkdec.2
    have hstep : ∀ s : ℕ, s < (k - mmLo t r x).toNat →
        ((x, mmLo t r x + (s : ℤ) + 1) : MMAlpha t) ∈ mmDecSet t r := by
      intro s hs
      have h2 : ((s : ℤ)) < ((k - mmLo t r x).toNat : ℤ) := by exact_mod_cast hs
      rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ k - mmLo t r x)] at h2
      show mmLo t r x ≤ mmLo t r x + (s : ℤ) + 1 ∧ mmLo t r x + (s : ℤ) + 1 ≤ mmHi t r x
      have hs0 : (0 : ℤ) ≤ (s : ℤ) := by exact_mod_cast Nat.zero_le s
      constructor
      · omega
      · have h3 : mmLo t r x + (s : ℤ) + 1 ≤ k := by omega
        omega
    have hchain := mmChain (r := r) hFw hc hA hB x (mmLo t r x) (mmLo_mem_decSet t r x)
      ((k - mmLo t r x).toNat) hstep
    have hsum : mmLo t r x + ((((k - mmLo t r x).toNat : ℕ) : ℤ)) = k := by
      rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ k - mmLo t r x)]
      ring
    rw [hsum] at hchain
    set X : mmK t r hFw hc hA hB :=
      HNNExtension.of (PresentedGroup.of (mmBetaOf t r ((x, mmLo t r x) : MMAlpha t))) with hX
    rw [mmRhoFun, map_mul, map_mul, map_zpow, map_zpow]
    simp only [FreeGroup.lift_apply_of, mmThetaFun_t (r := r) hFw hc hA hB]
    rw [mmThetaFun_ne (r := r) hFw hc hA hB (y := (x : α)) x.2]
    rw [show (HNNExtension.t : mmK t r hFw hc hA hB) ^ k *
          ((HNNExtension.t : mmK t r hFw hc hA hB) ^ (-(mmLo t r x)) * X *
            (HNNExtension.t : mmK t r hFw hc hA hB) ^ (mmLo t r x)) *
          (HNNExtension.t : mmK t r hFw hc hA hB) ^ (-k)
        = (HNNExtension.t : mmK t r hFw hc hA hB) ^ (((k - mmLo t r x).toNat : ℕ) : ℤ) * X *
          (HNNExtension.t : mmK t r hFw hc hA hB) ^ (-(((k - mmLo t r x).toNat : ℕ) : ℤ)) from by
      rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ k - mmLo t r x)]
      group]
    rw [hchain]
    have heq : mmBetaOf t r ((x, k) : MMAlpha t) = e :=
      Subtype.ext (by rw [mmBetaOf_val t r hkdec])
    rw [heq]
    rfl
  exact congrArg (fun f : FreeGroup (mmBeta t r) →* mmK t r hFw hc hA hB => f w) hcomp

end Tracking

end Work.OROneRel.EpsV2
