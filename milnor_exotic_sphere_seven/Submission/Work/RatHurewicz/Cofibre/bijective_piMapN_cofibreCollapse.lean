import Mathlib
import Submission.Work.RatHurewicz.Cofibre.StableRangeDefs
import Submission.Work.RatHurewicz.Cofibre.BMInstantiate
import Submission.Work.RatHurewicz.Cofibre.PiE
import Submission.Work.Serre.bijective_piMapN_of_joined
import Submission.Work.RatHurewicz.Cofibre.pi_one_E_of_fibration
import Submission.Work.RatHurewicz.relPiVanishing_of_isHurewiczFibration
import Submission.Work.RatHurewicz.relPiVanishingOfPiInjSurj
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.RatHurewicz.Cofibre.collapseAux
import Submission.Work.RatHurewicz.Cofibre.compressRel_cofibre_range_zero
import Submission.Work.RatHurewicz.LESConsequences
import Submission.Work.Cofibre.pathConnectedSpace_E_of_fibration
import Submission.Work.StemsB.fibration_les
import Submission.Work.StemsB.PiMap
import Submission.Work.RatHurewicz.Cofibre.subsingleton_relPi_cofibreU_collar
import Submission.Work.RatHurewicz.Cofibre.subsingleton_relPi_interInclLeft_wide

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000
open scoped Topology unitInterval

namespace Work.RatHurewicz.Cofibre

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- Elementary: if `f ∘ g = h` with `g` and `h` bijective then `f` is bijective. -/
theorem bijective_of_comp_eq {α β γ : Type} (f : β → γ) (g : α → β) (h : α → γ)
    (heq : f ∘ g = h) (hg : Function.Bijective g) (hh : Function.Bijective h) :
    Function.Bijective f := by
  constructor
  · intro y₁ y₂ hy
    obtain ⟨a₁, rfl⟩ := hg.2 y₁
    obtain ⟨a₂, rfl⟩ := hg.2 y₂
    have hy' : h a₁ = h a₂ := by
      rw [← congrFun heq a₁, ← congrFun heq a₂]
      exact hy
    exact congrArg g (hh.1 hy')
  · intro y
    obtain ⟨a, ha⟩ := hh.2 y
    refine ⟨g a, ?_⟩
    change (f ∘ g) a = y
    rw [congrFun heq a]
    exact ha

/-- Every point of the cofibre is joined to the base point. -/
theorem joined_cofibre (p : C(E, B)) (hp : Work.StemsB.IsHurewiczFibration p) (e₀ : E) (k : ℕ)
    (hk : 2 ≤ k)
    (hmodel : ∀ j : ℕ, j ≤ 2 * k - 1 → j ≠ k →
      Subsingleton (HomotopyGroup (Fin j) B (p e₀)))
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (↥(p ⁻¹' {p e₀}))
      ⟨e₀, rfl⟩))
    (z : Work.RatHurewicz.cofibre (setIncl (p ⁻¹' {p e₀}))) :
    Joined z (cofibreIncl (setIncl (p ⁻¹' {p e₀})) e₀) := by
  have hE : PathConnectedSpace E :=
    Work.Cofibre.pathConnectedSpace_E_of_fibration p hp e₀ k hk hconn hmodel
  obtain ⟨b, hbz⟩ := Work.RatHurewicz.exists_path_to_range (setIncl (p ⁻¹' {p e₀})) z
  obtain ⟨γ⟩ := hbz
  obtain ⟨x, hx⟩ := Set.mem_range.mp b.2
  obtain ⟨δ⟩ := hE.joined x e₀
  refine ⟨?_⟩
  exact γ.trans ((δ.map (cofibreIncl (setIncl (p ⁻¹' {p e₀}))).continuous).cast hx.symm rfl)

/-- `π_{j}(p) : π_j(E) → π_j(B)` is bijective for `1 ≤ j ≤ k`. -/
private theorem bijective_pimap_fibration (p : C(E, B)) (hp : Work.StemsB.IsHurewiczFibration p)
    (e₀ : E) (k : ℕ) (hk : 2 ≤ k)
    (hmodel : ∀ j : ℕ, j ≤ 2 * k - 1 → j ≠ k →
      Subsingleton (HomotopyGroup (Fin j) B (p e₀)))
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (↥(p ⁻¹' {p e₀}))
      ⟨e₀, rfl⟩))
    (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    Function.Bijective (Work.StemsB.πmap p (j - 1) e₀) := by
  rcases Nat.eq_or_lt_of_le hj1 with h1 | h1
  · subst h1
    haveI : Subsingleton (HomotopyGroup (Fin 1) E e₀) :=
      Work.RatHurewicz.Cofibre.pi_one_E_of_fibration p hp e₀ k hk hconn hmodel
    haveI : Subsingleton (HomotopyGroup (Fin 1) B (p e₀)) := hmodel 1 (by omega) (by omega)
    exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨1, Subsingleton.elim _ _⟩⟩
  · have hj2 : 2 ≤ j := h1
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
    change Function.Bijective (Work.StemsB.πmap p (m + 1) e₀)
    have hrel : ∀ k', Work.StemsB.HasHLPRel p k' :=
      fun k' => Work.StemsB.exists_lift_rel p hp.isSerreFibration k'
    have hf2 : Subsingleton (HomotopyGroup (Fin (m + 2)) (↥(p ⁻¹' {p e₀})) ⟨e₀, rfl⟩) :=
      hconn (m + 2) (by omega)
    have hf1 : Subsingleton (HomotopyGroup (Fin (m + 1)) (↥(p ⁻¹' {p e₀})) ⟨e₀, rfl⟩) :=
      hconn (m + 1) (by omega)
    constructor
    · intro a b hab
      have hE := Work.StemsB.les_exact_E p e₀ hrel m
      have key : ∀ a : HomotopyGroup (Fin (m + 2)) E e₀,
          Work.StemsB.πmap p (m + 1) e₀ a = 1 → a = 1 := by
        intro a ha
        obtain ⟨z, hz⟩ := (hE a).mp ha
        have hz1 : z = 1 := hf2.elim z 1
        rw [← hz, hz1]
        exact map_one _
      have h2 : a * b⁻¹ = 1 := key (a * b⁻¹) (by rw [map_mul, map_inv, hab, mul_inv_cancel])
      exact mul_inv_eq_one.mp h2
    · intro y
      have hB := Work.StemsB.les_exact_B p e₀ hrel m
      have hd : Work.StemsB.dMap p e₀ hrel m y = 1 := hf1.elim _ 1
      obtain ⟨x, hx⟩ := (hB y).mp hd
      exact ⟨x, hx⟩

/-- The composite `c ∘ (U ↪ C)` is homotopic to `p ∘ ρ`: both factor through `E` and
`ε ∘ ρ ~ id_U`. -/
private theorem homotopic_collapse_comp_retract {F : Type} [TopologicalSpace F] [Nonempty F]
    [Nonempty E] (ι : C(F, E)) (p : C(E, B)) (e₀ : E) (hb : ∀ y, p (ι y) = p e₀) :
    ((cofibreCollapse ι p (p e₀) hb).comp (setIncl (cofibreU ι))).Homotopic
      (p.comp (cofibreURetract ι e₀)) := by
  let f : C(↥(cofibreU ι), B) := (cofibreCollapse ι p (p e₀) hb).comp (setIncl (cofibreU ι))
  let g : C(↥(cofibreU ι), B) := p.comp (cofibreURetract ι e₀)
  have hε : ((cofibreUIncl ι).comp (cofibreURetract ι e₀)).Homotopic
      (ContinuousMap.id ↥(cofibreU ι)) := (cofibreUHomotopyEquiv ι e₀).left_inv
  have hρe : ∀ e : E, (cofibreURetract ι e₀) ((cofibreUIncl ι) e) = e := fun e =>
    congrFun (congrArg (fun k : C(E, E) => ⇑k) (cofibreURetract_comp_cofibreUIncl ι e₀)) e
  have heq : f.comp (cofibreUIncl ι) = g.comp (cofibreUIncl ι) := by
    apply ContinuousMap.ext
    intro e
    have h1 : f ((cofibreUIncl ι) e) = p e := by
      show (cofibreCollapse ι p (p e₀) hb) (cofibreIncl ι e) = p e
      exact cofibreCollapse_incl ι p (p e₀) hb e
    have h2 : g ((cofibreUIncl ι) e) = p e := by
      show p ((cofibreURetract ι e₀) ((cofibreUIncl ι) e)) = p e
      rw [hρe e]
    show f ((cofibreUIncl ι) e) = g ((cofibreUIncl ι) e)
    rw [h1, h2]
  have h1 : (f.comp (ContinuousMap.id _)).Homotopic
      (f.comp ((cofibreUIncl ι).comp (cofibreURetract ι e₀))) :=
    ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl f) hε.symm
  have h2 : (g.comp ((cofibreUIncl ι).comp (cofibreURetract ι e₀))).Homotopic
      (g.comp (ContinuousMap.id _)) :=
    (ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl g) hε.symm).symm
  have h3 : (f.comp ((cofibreUIncl ι).comp (cofibreURetract ι e₀))).Homotopic
      (g.comp ((cofibreUIncl ι).comp (cofibreURetract ι e₀))) := by
    have hassoc : f.comp ((cofibreUIncl ι).comp (cofibreURetract ι e₀))
        = g.comp ((cofibreUIncl ι).comp (cofibreURetract ι e₀)) := by
      rw [← ContinuousMap.comp_assoc, ← ContinuousMap.comp_assoc, heq]
    rw [← hassoc]
  have hmain : (f.comp (ContinuousMap.id _)).Homotopic (g.comp (ContinuousMap.id _)) :=
    h1.trans (h3.trans h2)
  rwa [ContinuousMap.comp_id f, ContinuousMap.comp_id g] at hmain

/-- `π_j(c) : π_j(cofibre ι) → π_j(B)` is bijective at the collar point, for `2 ≤ j ≤ k`. -/
private theorem bijective_pimap_collapse_low (p : C(E, B)) (hp : Work.StemsB.IsHurewiczFibration p)
    (e₀ : E) (k : ℕ) (hk : 2 ≤ k)
    (hmodel : ∀ j : ℕ, j ≤ 2 * k - 1 → j ≠ k →
      Subsingleton (HomotopyGroup (Fin j) B (p e₀)))
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (↥(p ⁻¹' {p e₀}))
      ⟨e₀, rfl⟩))
    (j : ℕ) (hj2 : 2 ≤ j) (hjk : j ≤ k) :
    Function.Bijective (Work.StemsB.πmap
      (cofibreCollapse (setIncl (p ⁻¹' {p e₀})) p (p e₀) (fun y => y.2)) (j - 1)
      ((collarPt (setIncl (p ⁻¹' {p e₀})) ⟨e₀, rfl⟩ : ↥(cofibreU (setIncl (p ⁻¹' {p e₀}))
        ∩ cofibreV (setIncl (p ⁻¹' {p e₀})))) : cofibre (setIncl (p ⁻¹' {p e₀})))) := by
  haveI : Nonempty E := ⟨e₀⟩
  haveI : Nonempty ↥(p ⁻¹' {p e₀}) := ⟨⟨e₀, rfl⟩⟩
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  let U : C(↥(cofibreU (setIncl (p ⁻¹' {p e₀}))), cofibre (setIncl (p ⁻¹' {p e₀}))) :=
    setIncl (cofibreU (setIncl (p ⁻¹' {p e₀})))
  let c : C(cofibre (setIncl (p ⁻¹' {p e₀})), B) :=
    cofibreCollapse (setIncl (p ⁻¹' {p e₀})) p (p e₀) (fun y => y.2)
  let ρ : C(↥(cofibreU (setIncl (p ⁻¹' {p e₀}))), E) :=
    cofibreURetract (setIncl (p ⁻¹' {p e₀})) e₀
  let x₀ : ↥(cofibreU (setIncl (p ⁻¹' {p e₀})) ∩ cofibreV (setIncl (p ⁻¹' {p e₀}))) :=
    collarPt (setIncl (p ⁻¹' {p e₀})) ⟨e₀, rfl⟩
  let x₀U : ↥(cofibreU (setIncl (p ⁻¹' {p e₀}))) := ⟨x₀.1, x₀.2.1⟩
  have hρ : Function.Bijective (Work.StemsB.πmap ρ (m + 1) x₀U) :=
    bijective_pimap_of_homotopyEquiv (cofibreUHomotopyEquiv (setIncl (p ⁻¹' {p e₀})) e₀)
      (m + 1) x₀U
  have hp' : Function.Bijective (Work.StemsB.πmap p (m + 1) e₀) :=
    bijective_pimap_fibration p hp e₀ k hk hmodel hconn (m + 2) (by omega) (by omega)
  have hEpc : PathConnectedSpace E :=
    Work.Cofibre.pathConnectedSpace_E_of_fibration p hp e₀ k hk hconn hmodel
  have hp'' : Function.Bijective (Work.StemsB.πmap p (m + 1) (ρ x₀U)) := by
    have hbr : ∀ x : E, Work.Serre.piMapN p (m + 2) x = Work.StemsB.πmap p (m + 1) x := by
      intro x
      rw [Work.Serre.piMapN_eq_homotopyGroupMap, πmap_eq_map]
    have h := Work.Serre.bijective_piMapN_of_joined p (hEpc.joined (ρ x₀U) e₀).symm (m + 2)
      (by rw [hbr]; exact hp')
    rwa [hbr] at h
  have hpρ : Function.Bijective (Work.StemsB.πmap (p.comp ρ) (m + 1) x₀U) := by
    have hfun : ⇑(Work.StemsB.πmap (p.comp ρ) (m + 1) x₀U)
        = fun a => Work.StemsB.πmap p (m + 1) (ρ x₀U)
            (Work.StemsB.πmap ρ (m + 1) x₀U a) := by
      funext a
      rw [Work.StemsB.πmap_comp_apply]
    rw [hfun]
    exact hp''.comp hρ
  obtain ⟨hH⟩ := homotopic_collapse_comp_retract (setIncl (p ⁻¹' {p e₀})) p e₀ (fun y => y.2)
  have hcU : Function.Bijective (Work.StemsB.πmap (c.comp U) (m + 1) x₀U) :=
    bijective_pimap_of_homotopic hH.symm (m + 1) x₀U hpρ
  have hU : Function.Bijective (Work.StemsB.πmap U (m + 1) x₀U) :=
    bijective_πmap_of_relPi_subsingleton U x₀U (m + 1) (by omega)
      (subsingleton_relPi_cofibreU_collar p hp e₀ k hk hmodel hconn (m + 1) (by omega)
        (by omega))
      (subsingleton_relPi_cofibreU_collar p hp e₀ k hk hmodel hconn (m + 2) (by omega)
        (by omega))
  have hdecomp : (⇑(Work.StemsB.πmap c (m + 1) (x₀ : cofibre (setIncl (p ⁻¹' {p e₀}))))
        ∘ ⇑(Work.StemsB.πmap U (m + 1) x₀U))
      = ⇑(Work.StemsB.πmap (c.comp U) (m + 1) x₀U) := by
    funext a
    show ⇑(Work.StemsB.πmap c (m + 1) (x₀ : cofibre (setIncl (p ⁻¹' {p e₀}))))
        (⇑(Work.StemsB.πmap U (m + 1) x₀U) a)
      = ⇑(Work.StemsB.πmap (c.comp U) (m + 1) x₀U) a
    rw [Work.StemsB.πmap_comp_apply]
    rfl
  exact bijective_of_comp_eq _ _ _ hdecomp hU hcU

/-- The Blakers–Massey conclusion: the relative groups of `(cofibre ι, V)` vanish. -/
private theorem subsingleton_relPi_cofibreV_collar (p : C(E, B))
    (hp : Work.StemsB.IsHurewiczFibration p) (e₀ : E) (k : ℕ) (hk : 2 ≤ k)
    (hmodel : ∀ j : ℕ, j ≤ 2 * k - 1 → j ≠ k →
      Subsingleton (HomotopyGroup (Fin j) B (p e₀)))
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (↥(p ⁻¹' {p e₀}))
      ⟨e₀, rfl⟩))
    (J : ℕ) (hJ1 : 1 ≤ J) (hJ : J ≤ 2 * k - 2) (hJk : J ≠ k - 1) :
    Subsingleton (RelHomotopyGroup (setIncl (cofibreV (setIncl (p ⁻¹' {p e₀}))))
      ⟨(collarPt (setIncl (p ⁻¹' {p e₀})) ⟨e₀, rfl⟩).1,
        (collarPt (setIncl (p ⁻¹' {p e₀})) ⟨e₀, rfl⟩).2.2⟩ J) := by
  haveI : Nonempty E := ⟨e₀⟩
  haveI : Nonempty ↥(p ⁻¹' {p e₀}) := ⟨⟨e₀, rfl⟩⟩
  let ι := setIncl (p ⁻¹' {p e₀})
  let x₀ : ↥(cofibreU ι ∩ cofibreV ι) := collarPt ι ⟨e₀, rfl⟩
  refine subsingleton_relPi_cofibreV_of_blakersMassey ι k x₀ ?_ ?_ ?_ J hJ1 hJ hJk
  · intro J' hJ'
    exact subsingleton_relPi_interInclLeft_wide p hp e₀ k hk hmodel hconn J'
      (by omega) (by omega)
  · intro J' hJ'
    refine subsingleton_relPi_interInclRight_of_conn ι J' x₀ ?_ ?_
    · obtain ⟨H, h0, b, h1⟩ := exists_contraction_cofibreV ι
      exact subsingleton_homotopyGroup_of_contraction'' H b h0 h1 _
    · obtain ⟨e⟩ := collarHomotopyEquiv ι
      rcases Nat.eq_zero_or_pos J' with h0 | hpos
      · subst h0
        have hF : Subsingleton (ZerothHomotopy ↥(p ⁻¹' {p e₀})) :=
          (pathConnectedSpace_iff_zerothHomotopy.mp
            (Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero ⟨e₀, rfl⟩
              (hconn 0 (by omega)))).2
        haveI : Subsingleton (ZerothHomotopy ↥(cofibreU ι ∩ cofibreV ι)) :=
          Work.RatHurewicz.subsingleton_zerothHomotopy_of_homotopyEquiv e hF
        exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (x := x₀)).injective
          (Subsingleton.elim _ _)⟩
      · haveI : Nonempty (Fin J') := ⟨⟨0, hpos⟩⟩
        exact (subsingleton_homotopyGroup_of_homotopyEquiv (N := Fin J') e x₀).mpr
          (subsingleton_pi_fibre_of_mem p e₀ k hconn J' hJ' (e.toFun x₀))
  · intro J' hJ's hJ'k
    exact subsingleton_relPi_interInclLeft_wide p hp e₀ k hk hmodel hconn J' hJ's hJ'k

/-- `π_j(cofibre ι)` is trivial at the collar point, for `3 ≤ j ≤ 2k-1`, `j ≠ k`. -/
private theorem subsingleton_pi_cofibre_high (p : C(E, B))
    (hp : Work.StemsB.IsHurewiczFibration p) (e₀ : E) (k : ℕ) (hk : 2 ≤ k)
    (hmodel : ∀ j : ℕ, j ≤ 2 * k - 1 → j ≠ k →
      Subsingleton (HomotopyGroup (Fin j) B (p e₀)))
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (↥(p ⁻¹' {p e₀}))
      ⟨e₀, rfl⟩))
    (j : ℕ) (hj3 : 3 ≤ j) (hjk2 : j ≤ 2 * k - 1) (hjk : j ≠ k) :
    Subsingleton (HomotopyGroup (Fin j) (cofibre (setIncl (p ⁻¹' {p e₀})))
      ((collarPt (setIncl (p ⁻¹' {p e₀})) ⟨e₀, rfl⟩ : ↥(cofibreU (setIncl (p ⁻¹' {p e₀}))
        ∩ cofibreV (setIncl (p ⁻¹' {p e₀})))) : cofibre (setIncl (p ⁻¹' {p e₀})))) := by
  haveI : Nonempty E := ⟨e₀⟩
  haveI : Nonempty ↥(p ⁻¹' {p e₀}) := ⟨⟨e₀, rfl⟩⟩
  let ι := setIncl (p ⁻¹' {p e₀})
  let x₀ : ↥(cofibreU ι ∩ cofibreV ι) := collarPt ι ⟨e₀, rfl⟩
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  have hm1 : 1 ≤ m := by omega
  refine Work.RatHurewicz.pi_subsingleton_of_relPi_subsingleton (setIncl (cofibreV ι))
    ⟨x₀.1, x₀.2.2⟩ m hm1 ?_ ?_
  · obtain ⟨H, h0, b, h1⟩ := exists_contraction_cofibreV ι
    exact subsingleton_homotopyGroup_of_contraction'' H b h0 h1 _
  · exact subsingleton_relPi_cofibreV_collar p hp e₀ k hk hmodel hconn (m + 1) (by omega)
      (by omega) (by omega)

/-- `π_1(cofibre ι)` is trivial at the base point. -/
private theorem subsingleton_pi_one_collapse (p : C(E, B))
    (hp : Work.StemsB.IsHurewiczFibration p) (e₀ : E) (k : ℕ) (hk : 2 ≤ k)
    (hmodel : ∀ j : ℕ, j ≤ 2 * k - 1 → j ≠ k →
      Subsingleton (HomotopyGroup (Fin j) B (p e₀)))
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (↥(p ⁻¹' {p e₀}))
      ⟨e₀, rfl⟩)) :
    Subsingleton (HomotopyGroup (Fin 1) (cofibre (setIncl (p ⁻¹' {p e₀})))
      (cofibreIncl (setIncl (p ⁻¹' {p e₀})) e₀)) := by
  haveI : Nonempty E := ⟨e₀⟩
  haveI : Nonempty ↥(p ⁻¹' {p e₀}) := ⟨⟨e₀, rfl⟩⟩
  let ι := setIncl (p ⁻¹' {p e₀})
  have hcomp : ∀ d, d ≤ 1 → Work.RatHurewicz.CompressRel (cofibre ι)
      (Set.range ⇑(cofibreIncl ι)) d :=
    compressRel_cofibre_range_zero ι ⟨e₀, rfl⟩ (hconn 0 (by omega))
  have hmemU : ∀ a : ↥(Set.range ⇑(cofibreIncl ι)), a.1 ∈ cofibreU ι := by
    rintro ⟨z, e, rfl⟩
    exact cofibreIncl_mem_cofibreU ι e
  let ψ : C(↥(Set.range ⇑(cofibreIncl ι)), E) :=
    ⟨fun a => cofibreURetract ι e₀ ⟨a.1, hmemU a⟩, by
      refine (cofibreURetract ι e₀).continuous.comp ?_
      exact Continuous.subtype_mk continuous_subtype_val _⟩
  have hψ_comp : ∀ e : E, cofibreURetract ι e₀
      ⟨cofibreIncl ι e, hmemU ⟨cofibreIncl ι e, ⟨e, rfl⟩⟩⟩ = e := by
    intro e
    exact congrFun (congrArg (fun k : C(E, E) => ⇑k) (cofibreURetract_comp_cofibreUIncl ι e₀)) e
  have hψS : ∀ b : ↥(Set.range ⇑(cofibreIncl ι)), cofibreIncl ι (ψ b) = b.1 := by
    rintro ⟨z, ⟨e, rfl⟩⟩
    show cofibreIncl ι ((cofibreURetract ι e₀) ⟨cofibreIncl ι e,
      hmemU ⟨cofibreIncl ι e, ⟨e, rfl⟩⟩⟩) = cofibreIncl ι e
    rw [hψ_comp e]
  have hψS₀ : ψ ⟨cofibreIncl ι e₀, ⟨e₀, rfl⟩⟩ = e₀ := hψ_comp e₀
  have hsurj := surjective_pimap_of_compressRel_range' (cofibreIncl ι) e₀ 1 hcomp ψ hψS hψS₀ 0
    (by omega)
  haveI : Subsingleton (HomotopyGroup (Fin 1) E e₀) :=
    Work.RatHurewicz.Cofibre.pi_one_E_of_fibration p hp e₀ k hk hconn hmodel
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, hy⟩ := hsurj b
  rw [← hy]
  exact congrArg _ (Subsingleton.elim x y)


theorem bijective_piMapN_cofibreCollapse {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsHurewiczFibration p) (e₀ : E) (k : ℕ) (hk : 2 ≤ k)
    (hmodel : ∀ j : ℕ, j ≤ 2 * k - 1 → j ≠ k →
      Subsingleton (HomotopyGroup (Fin j) B (p e₀)))
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (↥(p ⁻¹' {p e₀}))
      ⟨e₀, rfl⟩))
    (j : ℕ) (hj : j < 2 * k)
    (z : Work.RatHurewicz.cofibre (Work.RatHurewicz.setIncl (p ⁻¹' {p e₀}))) :
    Function.Bijective (Work.Serre.piMapN (Work.RatHurewicz.cofibreCollapse
      (Work.RatHurewicz.setIncl (p ⁻¹' {p e₀})) p (p e₀) (fun y => y.2)) j z) := by
  haveI : Nonempty E := ⟨e₀⟩
  haveI : Nonempty ↥(p ⁻¹' {p e₀}) := ⟨⟨e₀, rfl⟩⟩
  let c : C(cofibre (setIncl (p ⁻¹' {p e₀})), B) :=
    cofibreCollapse (setIncl (p ⁻¹' {p e₀})) p (p e₀) (fun y => y.2)
  have hz : Joined z (cofibreIncl (setIncl (p ⁻¹' {p e₀})) e₀) :=
    joined_cofibre p hp e₀ k hk hmodel hconn z
  suffices h : Function.Bijective
      (Work.Serre.piMapN c j (cofibreIncl (setIncl (p ⁻¹' {p e₀})) e₀)) from
    Work.Serre.bijective_piMapN_of_joined c hz.symm j h
  rcases j with _ | j'
  · -- `j = 0`
    have hpc : PathConnectedSpace (cofibre (setIncl (p ⁻¹' {p e₀}))) :=
      ⟨⟨cofibreIncl (setIncl (p ⁻¹' {p e₀})) e₀⟩, fun x y =>
        (joined_cofibre p hp e₀ k hk hmodel hconn x).trans
          (joined_cofibre p hp e₀ k hk hmodel hconn y).symm⟩
    haveI hZ : Subsingleton (ZerothHomotopy (cofibre (setIncl (p ⁻¹' {p e₀})))) :=
      (pathConnectedSpace_iff_zerothHomotopy.mp hpc).2
    haveI : Subsingleton (HomotopyGroup (Fin 0) (cofibre (setIncl (p ⁻¹' {p e₀})))
        (cofibreIncl (setIncl (p ⁻¹' {p e₀})) e₀)) :=
      ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy
        (x := cofibreIncl (setIncl (p ⁻¹' {p e₀})) e₀)).injective (Subsingleton.elim _ _)⟩
    haveI : Subsingleton (HomotopyGroup (Fin 0) B
        (c (cofibreIncl (setIncl (p ⁻¹' {p e₀})) e₀))) := by
      rw [show c (cofibreIncl (setIncl (p ⁻¹' {p e₀})) e₀) = p e₀ from
        cofibreCollapse_incl (setIncl (p ⁻¹' {p e₀})) p (p e₀) (fun y => y.2) e₀]
      exact hmodel 0 (by omega) (by omega)
    exact ⟨fun a b _ => Subsingleton.elim a b,
      fun b => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  · rcases j' with _ | j''
    · -- `j = 1`: the compression computation, at the base point
      haveI : Subsingleton (HomotopyGroup (Fin 1) (cofibre (setIncl (p ⁻¹' {p e₀})))
          (cofibreIncl (setIncl (p ⁻¹' {p e₀})) e₀)) :=
        subsingleton_pi_one_collapse p hp e₀ k hk hmodel hconn
      haveI : Subsingleton (HomotopyGroup (Fin 1) B
          (c (cofibreIncl (setIncl (p ⁻¹' {p e₀})) e₀))) := by
        rw [show c (cofibreIncl (setIncl (p ⁻¹' {p e₀})) e₀) = p e₀ from
          cofibreCollapse_incl (setIncl (p ⁻¹' {p e₀})) p (p e₀) (fun y => y.2) e₀]
        exact hmodel 1 (by omega) (by omega)
      exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨1, Subsingleton.elim _ _⟩⟩
    · -- `j = j'' + 2 ≥ 2`
      let x₀ : ↥(cofibreU (setIncl (p ⁻¹' {p e₀})) ∩ cofibreV (setIncl (p ⁻¹' {p e₀}))) :=
        collarPt (setIncl (p ⁻¹' {p e₀})) ⟨e₀, rfl⟩
      have hx₀ζ : Joined (x₀ : cofibre (setIncl (p ⁻¹' {p e₀})))
          (cofibreIncl (setIncl (p ⁻¹' {p e₀})) e₀) :=
        joined_cofibre p hp e₀ k hk hmodel hconn _
      have hbr : Work.Serre.piMapN c (j'' + 2) (x₀ : cofibre (setIncl (p ⁻¹' {p e₀})))
          = Work.StemsB.πmap c (j'' + 1) (x₀ : cofibre (setIncl (p ⁻¹' {p e₀}))) := by
        rw [Work.Serre.piMapN_eq_homotopyGroupMap, πmap_eq_map]
      have hx₀ : Function.Bijective
          (Work.Serre.piMapN c (j'' + 2) (x₀ : cofibre (setIncl (p ⁻¹' {p e₀})))) := by
        by_cases hjk : j'' + 2 ≤ k
        · -- low range
          have h := bijective_pimap_collapse_low p hp e₀ k hk hmodel hconn (j'' + 2)
            (by omega) hjk
          rw [hbr]
          exact h
        · -- high range: both groups are trivial
          have hC : Subsingleton (HomotopyGroup (Fin (j'' + 2))
              (cofibre (setIncl (p ⁻¹' {p e₀}))) (x₀ : cofibre (setIncl (p ⁻¹' {p e₀})))) :=
            subsingleton_pi_cofibre_high p hp e₀ k hk hmodel hconn (j'' + 2) (by omega)
              (by omega) (by omega)
          have hcx : c (x₀ : cofibre (setIncl (p ⁻¹' {p e₀}))) = p e₀ := by
            show (cofibreCollapse (setIncl (p ⁻¹' {p e₀})) p (p e₀) (fun y => y.2))
              (cofibreInclCone (setIncl (p ⁻¹' {p e₀}))
                (coneMk (⟨e₀, rfl⟩, collarStub))) = p e₀
            exact cofibreCollapse_cone (setIncl (p ⁻¹' {p e₀})) p (p e₀) (fun y => y.2)
              (coneMk (⟨e₀, rfl⟩, collarStub))
          have hB : Subsingleton (HomotopyGroup (Fin (j'' + 2)) B
              (c (x₀ : cofibre (setIncl (p ⁻¹' {p e₀}))))) := by
            rw [hcx]
            exact hmodel (j'' + 2) (by omega) (by omega)
          exact ⟨fun a b _ => Subsingleton.elim a b,
            fun b => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
      exact Work.Serre.bijective_piMapN_of_joined c hx₀ζ (j'' + 2) hx₀

end Work.RatHurewicz.Cofibre
