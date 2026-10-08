import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.Basic
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.commutatorElement_mul_of_abel_normal
import Submission.Work.Higman.clo_comm_expansion
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.HS.hard_two_cover

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open scoped commutatorElement

namespace Work.Commutator

/-- If `⁅a,x⁆` and `⁅a,y⁆` are central then `⁅a, x*y⁆ = ⁅a,y⁆ * ⁅a,x⁆`. -/
private lemma comm_mul_right_of_central {G : Type} [Group G] {a x y : G}
    (hx : ⁅a, x⁆ ∈ Subgroup.center G) (hy : ⁅a, y⁆ ∈ Subgroup.center G) :
    ⁅a, x * y⁆ = ⁅a, y⁆ * ⁅a, x⁆ := by
  have hxc : ∀ g : G, g * ⁅a, x⁆ = ⁅a, x⁆ * g := fun g => Subgroup.mem_center_iff.mp hx g
  have hyc : ∀ g : G, g * ⁅a, y⁆ = ⁅a, y⁆ * g := fun g => Subgroup.mem_center_iff.mp hy g
  calc ⁅a, x * y⁆ = ⁅a, x⁆ * x * ⁅a, y⁆ * x⁻¹ := commutatorElement_mul_right_eq_mul_conj a x y
    _ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by group
    _ = ⁅a, x⁆ * ⁅a, y⁆ := by rw [show x * ⁅a, y⁆ * x⁻¹ = ⁅a, y⁆ by rw [hyc x]; group]
    _ = ⁅a, y⁆ * ⁅a, x⁆ := hyc ⁅a, x⁆

/-- **The radical of the two-cover commutator pairing is trivial on `X`.**

Let `P` be a Suzuki 2-group and `A ⊴ P` `ξ`-invariant with `A ^ (2) = Ω₁(P)`, `|A| = |Ω₁(P)|²`
and `[⊤,⊤] = A`.  Let `X, Y` be subgroups with `A ≤ X`, `[X,X] = [Y,Y] = [X,A] = [Y,A] = A ^ (2)`,
`X ⊔ Y = ⊤`, `X` normal `ξ`-invariant and minimal over `A` among normal `ξ`-invariant subgroups.
Then any `x ∈ X` whose commutators with all of `Y` lie in `A ^ (2)` already lies in `A`. -/
private theorem radical_of_cover {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A X Y : Subgroup P} [hAn : A.Normal]
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hXn : X.Normal) (hXinv : X.map (h.xi : MulAut P).toMonoidHom = X)
    (hAX : A ≤ X)
    (hXcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ X → D = A ∨ D = X)
    (hXd : Bracket.bracket X X = Work.Higman.powSub A 2)
    (hYd : Bracket.bracket Y Y = Work.Higman.powSub A 2)
    (hXAd : Bracket.bracket X A = Work.Higman.powSub A 2)
    (hYAd : Bracket.bracket Y A = Work.Higman.powSub A 2)
    (hXYsup : X ⊔ Y = ⊤) :
    ∀ x ∈ X, (∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ Work.Higman.powSub A 2) → x ∈ A := by
  classical
  haveI : X.Normal := hXn
  -- `A ^ (2) = Ω₁(P)` is central
  have hZc : ∀ z : P, z ∈ Work.Higman.powSub A 2 → z ∈ Subgroup.center P := by
    intro z hz
    rw [htop] at hz
    exact h.omega1_le_center hz
  have hZcc : ∀ z ∈ Work.Higman.powSub A 2, ∀ g : P, g * z * g⁻¹ = z := by
    intro z hz g
    rw [Subgroup.mem_center_iff.mp (hZc z hz) g]
    group
  -- `P = X · Y`
  have hmem_sup : ∀ w : P, ∃ x ∈ X, ∃ y ∈ Y, x * y = w := fun w =>
    (Subgroup.mem_sup_of_normal_left (s := X) (t := Y)).mp (by
      rw [hXYsup]; exact Subgroup.mem_top w)
  -- commutators with `A` and with `X` land in `A ^ (2)`
  have hAX2 : ∀ a ∈ A, ∀ x ∈ X, ⁅a, x⁆ ∈ Work.Higman.powSub A 2 := by
    intro a ha x hx
    have hmem : ⁅a, x⁆ ∈ Bracket.bracket A X := Subgroup.commutator_mem_commutator ha hx
    rw [Subgroup.commutator_comm, hXAd] at hmem
    exact hmem
  have hAY2 : ∀ a ∈ A, ∀ y ∈ Y, ⁅a, y⁆ ∈ Work.Higman.powSub A 2 := by
    intro a ha y hy
    have hmem : ⁅a, y⁆ ∈ Bracket.bracket A Y := Subgroup.commutator_mem_commutator ha hy
    rw [Subgroup.commutator_comm, hYAd] at hmem
    exact hmem
  -- ## `A ≤ Erad h A`
  have hAEr : A ≤ Work.Higman.HS.Erad h A := by
    intro a ha
    rw [Work.Higman.HS.mem_Erad_iff]
    intro w
    obtain ⟨x, hx, y, hy, rfl⟩ := hmem_sup w
    have h1 : ⁅a, x⁆ ∈ Work.Higman.powSub A 2 := hAX2 a ha x hx
    have h2 : ⁅a, y⁆ ∈ Work.Higman.powSub A 2 := hAY2 a ha y hy
    have hgoal : ⁅a, x * y⁆ = ⁅a, y⁆ * ⁅a, x⁆ :=
      comm_mul_right_of_central (hZc _ h1) (hZc _ h2)
    rw [show a * (x * y) * a⁻¹ * (x * y)⁻¹ = ⁅a, x * y⁆ by rw [commutatorElement_def],
      hgoal]
    exact Subgroup.mul_mem _ h2 h1
  -- ## `X ≤ Erad h A` forces `Y ≤ Erad h A`
  have hYEr : X ≤ Work.Higman.HS.Erad h A → Y ≤ Work.Higman.HS.Erad h A := by
    intro hX
    intro y hy
    rw [Work.Higman.HS.mem_Erad_iff]
    intro w
    obtain ⟨x, hx, y', hy', rfl⟩ := hmem_sup w
    have h1 : ⁅y, y'⁆ ∈ Work.Higman.powSub A 2 := by
      have hmem : ⁅y, y'⁆ ∈ Bracket.bracket Y Y := Subgroup.commutator_mem_commutator hy hy'
      rwa [hYd] at hmem
    have h2 : ⁅y, x⁆ ∈ Work.Higman.powSub A 2 := by
      have hmem : ⁅x, y⁆ ∈ Work.Higman.powSub A 2 := by
        rw [commutatorElement_def]
        exact (Work.Higman.HS.mem_Erad_iff.mp (hX hx)) y
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ hmem
    have hgoal : ⁅y, x * y'⁆ = ⁅y, y'⁆ * ⁅y, x⁆ :=
      comm_mul_right_of_central (hZc _ h2) (hZc _ h1)
    rw [show y * (x * y') * y⁻¹ * (x * y')⁻¹ = ⁅y, x * y'⁆ by rw [commutatorElement_def],
      hgoal]
    exact Subgroup.mul_mem _ h1 h2
  -- ## `X ≰ Erad h A`
  have hnotle : ¬ (X ≤ Work.Higman.HS.Erad h A) := by
    intro hX
    have hY : Y ≤ Work.Higman.HS.Erad h A := hYEr hX
    have htop' : (⊤ : Subgroup P) ≤ Work.Higman.HS.Erad h A := by
      rw [← hXYsup]
      exact sup_le hX hY
    have hcc : Bracket.bracket (⊤ : Subgroup P) ⊤ ≤ Work.Higman.powSub A 2 := by
      rw [Subgroup.commutator_le]
      intro u _ v _
      have hh := (Work.Higman.HS.mem_Erad_iff.mp (htop' (Subgroup.mem_top v))) u
      rw [commutatorElement_def]
      rw [show u * v * u⁻¹ * v⁻¹ = (v * u * v⁻¹ * u⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ hh
    rw [hGs] at hcc
    exact Work.Higman.HS.ne_powSub_two_of_card h htop hcard
      (le_antisymm hcc (Work.Higman.powSub_le (by norm_num)))
  -- ## `Erad h A ⊓ X = A`
  have hRinfX : Work.Higman.HS.Erad h A ⊓ X = A := by
    have hErinv : (Work.Higman.HS.Erad h A).map (h.xi : MulAut P).toMonoidHom
        = Work.Higman.HS.Erad h A := Work.Higman.HS.map_xi_Erad hAxi
    have hIinv : (Work.Higman.HS.Erad h A ⊓ X).map (h.xi : MulAut P).toMonoidHom
        = Work.Higman.HS.Erad h A ⊓ X := by
      rw [Subgroup.map_inf _ _ _ (h.xi : MulAut P).injective, hErinv, hXinv]
    haveI : (Work.Higman.HS.Erad h A ⊓ X).Normal :=
      ⟨fun n hn g => ⟨Work.Higman.HS.Erad_normal.conj_mem n hn.1 g, hXn.conj_mem n hn.2 g⟩⟩
    rcases hXcover (Work.Higman.HS.Erad h A ⊓ X) inferInstance hIinv (le_inf hAEr hAX)
      inf_le_right with hh | hh
    · exact hh
    · apply absurd _ hnotle
      rw [← hh]
      exact inf_le_left
  -- ## The radical statement
  intro x hx hcomm
  have hxR : x ∈ Work.Higman.HS.Erad h A := by
    rw [Work.Higman.HS.mem_Erad_iff]
    intro w
    obtain ⟨x', hx', y', hy', rfl⟩ := hmem_sup w
    have h1 : ⁅x, x'⁆ ∈ Work.Higman.powSub A 2 := by
      have hmem : ⁅x, x'⁆ ∈ Bracket.bracket X X := Subgroup.commutator_mem_commutator hx hx'
      rwa [hXd] at hmem
    have h2 : ⁅x, y'⁆ ∈ Work.Higman.powSub A 2 := by
      rw [commutatorElement_def]
      exact hcomm y' hy'
    have hgoal : ⁅x, x' * y'⁆ = ⁅x, y'⁆ * ⁅x, x'⁆ :=
      comm_mul_right_of_central (hZc _ h1) (hZc _ h2)
    rw [show x * (x' * y') * x⁻¹ * (x' * y')⁻¹ = ⁅x, x' * y'⁆ by
      rw [commutatorElement_def], hgoal]
    exact Subgroup.mul_mem _ h2 h1
  rw [← hRinfX]
  exact ⟨hxR, hx⟩

/-- The commutator pairing `C/A × E/A → A/A²` of the two-cover configuration. -/
theorem two_cover_ce_pairing {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C E : Subgroup P} [hAn : A.Normal]
    [hN1 : ((Work.Higman.powSub A 2).subgroupOf A).Normal]
    [hN2 : (A.subgroupOf C).Normal] [hN3 : (A.subgroupOf E).Normal]
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hcent : Subgroup.centralizer (A : Set P) = A)
    (hCn : C.Normal) (hEn : E.Normal)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hEinv : E.map (h.xi : MulAut P).toMonoidHom = E)
    (hAC : A ≤ C) (hAE : A ≤ E)
    (hCcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hEcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ E → D = A ∨ D = E)
    (hCd : Bracket.bracket C C = Work.Higman.powSub A 2)
    (hEd : Bracket.bracket E E = Work.Higman.powSub A 2)
    (hCAd : Bracket.bracket C A = Work.Higman.powSub A 2)
    (hEAd : Bracket.bracket E A = Work.Higman.powSub A 2)
    (hCE : C ⊓ E = A) (hCEsup : C ⊔ E = ⊤) :
    ∃ B : (↥C ⧸ (A.subgroupOf C)) → (↥E ⧸ (A.subgroupOf E)) →
        (↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A),
      (∀ (c : ↥C) (e : ↥E) (a : ↥A),
        (a : P) = (c : P) * (e : P) * (c : P)⁻¹ * (e : P)⁻¹ →
        B (QuotientGroup.mk c) (QuotientGroup.mk e) = QuotientGroup.mk a) ∧
      (∀ x y z, B (x * y) z = B x z * B y z) ∧
      (∀ x y z, B x (y * z) = B x y * B x z) ∧
      (∀ x, x ≠ 1 → ∃ y, B x y ≠ 1) ∧
      (∀ y, y ≠ 1 → ∃ x, B x y ≠ 1) := by
  classical
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  have hAxi : A.map (h.xi : MulAut P).toMonoidHom = A := hA.map_eq
  -- `A ^ (2) = Ω₁(P)` is central in `P`
  have hZc : ∀ z : P, z ∈ Work.Higman.powSub A 2 → z ∈ Subgroup.center P := by
    intro z hz
    rw [htop] at hz
    exact h.omega1_le_center hz
  -- `⁅C,E⁆ ≤ A`
  have hCEA : Bracket.bracket C E ≤ A :=
    (Subgroup.commutator_mono le_top le_top).trans (le_of_eq hGs)
  have hmemA : ∀ (c : P), c ∈ C → ∀ (e : P), e ∈ E → ⁅c, e⁆ ∈ A := by
    intro c hc e he
    exact hCEA (Subgroup.commutator_mem_commutator hc he)
  -- ## The value of the pairing on representatives
  let Φ : ↥C → ↥E → (↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A) :=
    fun c e => QuotientGroup.mk (⟨⁅(c : P), (e : P)⁆, hmemA (c : P) c.2 (e : P) e.2⟩ : ↥A)
  -- ## Two elements of `A` differing by an element of `A ^ (2)` have the same image
  have mk_eq_of_mul_inv : ∀ {x y : ↥A},
      ((x : P) * (y : P)⁻¹ ∈ Work.Higman.powSub A 2) →
      QuotientGroup.mk (s := (Work.Higman.powSub A 2).subgroupOf A) x
        = QuotientGroup.mk (s := (Work.Higman.powSub A 2).subgroupOf A) y := by
    intro x y hxy
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have key : (x : P)⁻¹ * (y : P) = ((x : P) * (y : P)⁻¹)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
      exact hAab _ (A.inv_mem x.2) _ y.2
    rw [key]
    exact Subgroup.inv_mem _ hxy
  -- ## `Φ` is invariant under multiplication by `A` in the first variable
  have hΦL : ∀ (c : ↥C) (a : ↥A) (e : ↥E),
      Φ (c * ⟨(a : P), hAC a.2⟩) e = Φ c e := by
    intro c a e
    have hfact : ⁅(c : P) * (a : P), (e : P)⁆ * (⁅(a : P), (e : P)⁆ * ⁅(c : P), (e : P)⁆)⁻¹
        ∈ Work.Higman.powSub A 2 :=
      Work.Higman.clo_comm_mul_left h hA hGs (Subgroup.mem_top _) (Subgroup.mem_top _)
        (Subgroup.mem_top _)
    have hae : ⁅(a : P), (e : P)⁆ ∈ Work.Higman.powSub A 2 := by
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ (Work.Higman.commutator_mem_powSub_two h hA (e : P) (a : P) a.2)
    have hae1 : (QuotientGroup.mk (⟨⁅(a : P), (e : P)⁆,
          hmemA (a : P) (hAC a.2) (e : P) e.2⟩ : ↥A)
        : ↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hae
    have h1 : (QuotientGroup.mk (⟨⁅(c : P) * (a : P), (e : P)⁆,
          hmemA ((c : P) * (a : P)) (C.mul_mem c.2 (hAC a.2)) (e : P) e.2⟩ : ↥A)
        : ↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A)
        = QuotientGroup.mk ((⟨⁅(a : P), (e : P)⁆, hmemA (a : P) (hAC a.2) (e : P) e.2⟩ : ↥A)
            * ⟨⁅(c : P), (e : P)⁆, hmemA (c : P) c.2 (e : P) e.2⟩) := by
      apply mk_eq_of_mul_inv
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hfact
    calc Φ (c * ⟨(a : P), hAC a.2⟩) e
        = QuotientGroup.mk (⟨⁅(c : P) * (a : P), (e : P)⁆,
            hmemA ((c : P) * (a : P)) (C.mul_mem c.2 (hAC a.2)) (e : P) e.2⟩ : ↥A) := rfl
      _ = QuotientGroup.mk ((⟨⁅(a : P), (e : P)⁆, hmemA (a : P) (hAC a.2) (e : P) e.2⟩ : ↥A)
            * ⟨⁅(c : P), (e : P)⁆, hmemA (c : P) c.2 (e : P) e.2⟩) := h1
      _ = QuotientGroup.mk (⟨⁅(a : P), (e : P)⁆, hmemA (a : P) (hAC a.2) (e : P) e.2⟩ : ↥A)
            * QuotientGroup.mk (⟨⁅(c : P), (e : P)⁆, hmemA (c : P) c.2 (e : P) e.2⟩ : ↥A) :=
          QuotientGroup.mk_mul _ _ _
      _ = 1 * QuotientGroup.mk (⟨⁅(c : P), (e : P)⁆, hmemA (c : P) c.2 (e : P) e.2⟩ : ↥A) := by
          rw [hae1]
      _ = QuotientGroup.mk (⟨⁅(c : P), (e : P)⁆, hmemA (c : P) c.2 (e : P) e.2⟩ : ↥A) :=
          one_mul _
      _ = Φ c e := rfl
  -- ## `Φ` is invariant under multiplication by `A` in the second variable
  have hΦR : ∀ (c : ↥C) (e : ↥E) (a : ↥A),
      Φ c (e * ⟨(a : P), hAE a.2⟩) = Φ c e := by
    intro c e a
    have hfact : ⁅(c : P), (e : P) * (a : P)⁆ * (⁅(c : P), (e : P)⁆ * ⁅(c : P), (a : P)⁆)⁻¹
        ∈ Work.Higman.powSub A 2 :=
      Work.Higman.clo_comm_mul_right h hA hGs (Subgroup.mem_top _) (Subgroup.mem_top _)
        (Subgroup.mem_top _)
    have hca : ⁅(c : P), (a : P)⁆ ∈ Work.Higman.powSub A 2 :=
      Work.Higman.commutator_mem_powSub_two h hA (c : P) (a : P) a.2
    have hca1 : (QuotientGroup.mk (⟨⁅(c : P), (a : P)⁆,
          hmemA (c : P) c.2 (a : P) (hAE a.2)⟩ : ↥A)
        : ↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hca
    have h1 : (QuotientGroup.mk (⟨⁅(c : P), (e : P) * (a : P)⁆,
          hmemA (c : P) c.2 ((e : P) * (a : P)) (E.mul_mem e.2 (hAE a.2))⟩ : ↥A)
        : ↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A)
        = QuotientGroup.mk ((⟨⁅(c : P), (e : P)⁆, hmemA (c : P) c.2 (e : P) e.2⟩ : ↥A)
            * ⟨⁅(c : P), (a : P)⁆, hmemA (c : P) c.2 (a : P) (hAE a.2)⟩) := by
      apply mk_eq_of_mul_inv
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hfact
    calc Φ c (e * ⟨(a : P), hAE a.2⟩)
        = QuotientGroup.mk (⟨⁅(c : P), (e : P) * (a : P)⁆,
            hmemA (c : P) c.2 ((e : P) * (a : P)) (E.mul_mem e.2 (hAE a.2))⟩ : ↥A) := rfl
      _ = QuotientGroup.mk ((⟨⁅(c : P), (e : P)⁆, hmemA (c : P) c.2 (e : P) e.2⟩ : ↥A)
            * ⟨⁅(c : P), (a : P)⁆, hmemA (c : P) c.2 (a : P) (hAE a.2)⟩) := h1
      _ = QuotientGroup.mk (⟨⁅(c : P), (e : P)⁆, hmemA (c : P) c.2 (e : P) e.2⟩ : ↥A)
            * QuotientGroup.mk (⟨⁅(c : P), (a : P)⁆, hmemA (c : P) c.2 (a : P) (hAE a.2)⟩ : ↥A) :=
          QuotientGroup.mk_mul _ _ _
      _ = QuotientGroup.mk (⟨⁅(c : P), (e : P)⁆, hmemA (c : P) c.2 (e : P) e.2⟩ : ↥A) * 1 := by
          rw [hca1]
      _ = QuotientGroup.mk (⟨⁅(c : P), (e : P)⁆, hmemA (c : P) c.2 (e : P) e.2⟩ : ↥A) :=
          mul_one _
      _ = Φ c e := rfl
  -- ## Additivity of `Φ` in the first variable
  have hΦAL : ∀ (c₁ c₂ : ↥C) (e : ↥E), Φ (c₁ * c₂) e = Φ c₁ e * Φ c₂ e := by
    intro c₁ c₂ e
    have hfact : ⁅(c₁ : P) * (c₂ : P), (e : P)⁆ *
          (⁅(c₂ : P), (e : P)⁆ * ⁅(c₁ : P), (e : P)⁆)⁻¹ ∈ Work.Higman.powSub A 2 :=
      Work.Higman.clo_comm_mul_left h hA hGs (Subgroup.mem_top _) (Subgroup.mem_top _)
        (Subgroup.mem_top _)
    have h1 : (QuotientGroup.mk (⟨⁅(c₁ : P) * (c₂ : P), (e : P)⁆,
          hmemA ((c₁ : P) * (c₂ : P)) (C.mul_mem c₁.2 c₂.2) (e : P) e.2⟩ : ↥A)
        : ↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A)
        = QuotientGroup.mk ((⟨⁅(c₂ : P), (e : P)⁆, hmemA (c₂ : P) c₂.2 (e : P) e.2⟩ : ↥A)
            * ⟨⁅(c₁ : P), (e : P)⁆, hmemA (c₁ : P) c₁.2 (e : P) e.2⟩) := by
      apply mk_eq_of_mul_inv
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hfact
    have hswap : (QuotientGroup.mk (⟨⁅(c₂ : P), (e : P)⁆, hmemA (c₂ : P) c₂.2 (e : P) e.2⟩ : ↥A)
        : ↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A)
          * QuotientGroup.mk (⟨⁅(c₁ : P), (e : P)⁆, hmemA (c₁ : P) c₁.2 (e : P) e.2⟩ : ↥A)
        = QuotientGroup.mk (⟨⁅(c₁ : P), (e : P)⁆, hmemA (c₁ : P) c₁.2 (e : P) e.2⟩ : ↥A)
          * QuotientGroup.mk (⟨⁅(c₂ : P), (e : P)⁆, hmemA (c₂ : P) c₂.2 (e : P) e.2⟩ : ↥A) := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hAab _ (hmemA (c₂ : P) c₂.2 (e : P) e.2) _
        (hmemA (c₁ : P) c₁.2 (e : P) e.2))
    calc Φ (c₁ * c₂) e
        = QuotientGroup.mk (⟨⁅(c₁ : P) * (c₂ : P), (e : P)⁆,
            hmemA ((c₁ : P) * (c₂ : P)) (C.mul_mem c₁.2 c₂.2) (e : P) e.2⟩ : ↥A) := rfl
      _ = QuotientGroup.mk ((⟨⁅(c₂ : P), (e : P)⁆, hmemA (c₂ : P) c₂.2 (e : P) e.2⟩ : ↥A)
            * ⟨⁅(c₁ : P), (e : P)⁆, hmemA (c₁ : P) c₁.2 (e : P) e.2⟩) := h1
      _ = QuotientGroup.mk (⟨⁅(c₂ : P), (e : P)⁆, hmemA (c₂ : P) c₂.2 (e : P) e.2⟩ : ↥A)
            * QuotientGroup.mk (⟨⁅(c₁ : P), (e : P)⁆, hmemA (c₁ : P) c₁.2 (e : P) e.2⟩ : ↥A) :=
          QuotientGroup.mk_mul _ _ _
      _ = QuotientGroup.mk (⟨⁅(c₁ : P), (e : P)⁆, hmemA (c₁ : P) c₁.2 (e : P) e.2⟩ : ↥A)
            * QuotientGroup.mk (⟨⁅(c₂ : P), (e : P)⁆, hmemA (c₂ : P) c₂.2 (e : P) e.2⟩ : ↥A) :=
          hswap
      _ = Φ c₁ e * Φ c₂ e := rfl
  -- ## Additivity of `Φ` in the second variable
  have hΦAR : ∀ (c : ↥C) (e₁ e₂ : ↥E), Φ c (e₁ * e₂) = Φ c e₁ * Φ c e₂ := by
    intro c e₁ e₂
    have hfact : ⁅(c : P), (e₁ : P) * (e₂ : P)⁆ *
          (⁅(c : P), (e₁ : P)⁆ * ⁅(c : P), (e₂ : P)⁆)⁻¹ ∈ Work.Higman.powSub A 2 :=
      Work.Higman.clo_comm_mul_right h hA hGs (Subgroup.mem_top _) (Subgroup.mem_top _)
        (Subgroup.mem_top _)
    have h1 : (QuotientGroup.mk (⟨⁅(c : P), (e₁ : P) * (e₂ : P)⁆,
          hmemA (c : P) c.2 ((e₁ : P) * (e₂ : P)) (E.mul_mem e₁.2 e₂.2)⟩ : ↥A)
        : ↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A)
        = QuotientGroup.mk ((⟨⁅(c : P), (e₁ : P)⁆, hmemA (c : P) c.2 (e₁ : P) e₁.2⟩ : ↥A)
            * ⟨⁅(c : P), (e₂ : P)⁆, hmemA (c : P) c.2 (e₂ : P) e₂.2⟩) := by
      apply mk_eq_of_mul_inv
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hfact
    calc Φ c (e₁ * e₂)
        = QuotientGroup.mk (⟨⁅(c : P), (e₁ : P) * (e₂ : P)⁆,
            hmemA (c : P) c.2 ((e₁ : P) * (e₂ : P)) (E.mul_mem e₁.2 e₂.2)⟩ : ↥A) := rfl
      _ = QuotientGroup.mk ((⟨⁅(c : P), (e₁ : P)⁆, hmemA (c : P) c.2 (e₁ : P) e₁.2⟩ : ↥A)
            * ⟨⁅(c : P), (e₂ : P)⁆, hmemA (c : P) c.2 (e₂ : P) e₂.2⟩) := h1
      _ = QuotientGroup.mk (⟨⁅(c : P), (e₁ : P)⁆, hmemA (c : P) c.2 (e₁ : P) e₁.2⟩ : ↥A)
            * QuotientGroup.mk (⟨⁅(c : P), (e₂ : P)⁆, hmemA (c : P) c.2 (e₂ : P) e₂.2⟩ : ↥A) :=
          QuotientGroup.mk_mul _ _ _
      _ = Φ c e₁ * Φ c e₂ := rfl
  -- ## Descent to the quotient in the second variable
  have wdR : ∀ (c : ↥C) (e₁ e₂ : ↥E),
      QuotientGroup.leftRel (A.subgroupOf E) e₁ e₂ → Φ c e₁ = Φ c e₂ := by
    intro c e₁ e₂ hrel
    have hz : (e₁ : P)⁻¹ * (e₂ : P) ∈ A :=
      Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hrel)
    have heq : (e₂ : P) = (e₁ : P) * ((e₁ : P)⁻¹ * (e₂ : P)) := by group
    have he2 : e₂ = e₁ * ⟨(e₁ : P)⁻¹ * (e₂ : P), hAE hz⟩ := Subtype.ext heq
    rw [he2]
    exact (hΦR c e₁ ⟨(e₁ : P)⁻¹ * (e₂ : P), hz⟩).symm
  -- ## Descent to the quotient in the first variable
  have wdL : ∀ (c₁ c₂ : ↥C), QuotientGroup.leftRel (A.subgroupOf C) c₁ c₂ →
      (fun y : ↥E ⧸ (A.subgroupOf E) => Quotient.liftOn y (Φ c₁) (wdR c₁))
        = (fun y : ↥E ⧸ (A.subgroupOf E) => Quotient.liftOn y (Φ c₂) (wdR c₂)) := by
    intro c₁ c₂ hrel
    have hz : (c₁ : P)⁻¹ * (c₂ : P) ∈ A :=
      Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hrel)
    have heq : (c₂ : P) = (c₁ : P) * ((c₁ : P)⁻¹ * (c₂ : P)) := by group
    have hc2 : c₂ = c₁ * ⟨(c₁ : P)⁻¹ * (c₂ : P), hAC hz⟩ := Subtype.ext heq
    funext y
    induction y using QuotientGroup.induction_on with
    | _ e =>
      show Φ c₁ e = Φ c₂ e
      rw [hc2]
      exact (hΦL c₁ ⟨(c₁ : P)⁻¹ * (c₂ : P), hz⟩ e).symm
  -- ## The pairing
  let B : (↥C ⧸ (A.subgroupOf C)) → (↥E ⧸ (A.subgroupOf E)) →
      (↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A) :=
    fun x => Quotient.liftOn x (fun c : ↥C => fun y => Quotient.liftOn y (Φ c) (wdR c)) wdL
  have hBdef : ∀ (c : ↥C) (e : ↥E), B (QuotientGroup.mk c) (QuotientGroup.mk e) = Φ c e :=
    fun c e => rfl
  -- ## The two radicals
  have radC : ∀ x ∈ C, (∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ Work.Higman.powSub A 2) → x ∈ A :=
    radical_of_cover h hAxi hGs htop hcard hCn hCinv hAC hCcover hCd hEd hCAd hEAd hCEsup
  have radE : ∀ x ∈ E, (∀ y ∈ C, x * y * x⁻¹ * y⁻¹ ∈ Work.Higman.powSub A 2) → x ∈ A :=
    radical_of_cover h hAxi hGs htop hcard hEn hEinv hAE hEcover hEd hCd hEAd hCAd
      (by rw [sup_comm]; exact hCEsup)
  refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
  · -- the values of `B` are the commutators
    intro c e a ha
    rw [hBdef]
    rw [show Φ c e = QuotientGroup.mk (⟨⁅(c : P), (e : P)⁆,
      hmemA (c : P) c.2 (e : P) e.2⟩ : ↥A) from rfl]
    rw [show (⟨⁅(c : P), (e : P)⁆, hmemA (c : P) c.2 (e : P) e.2⟩ : ↥A) = a from
      Subtype.ext (by
        show (c : P) * (e : P) * (c : P)⁻¹ * (e : P)⁻¹ = (a : P)
        exact ha.symm)]
  · -- additivity in the first variable
    intro x
    induction x using QuotientGroup.induction_on with
    | _ c₁ =>
      intro y
      induction y using QuotientGroup.induction_on with
      | _ c₂ =>
        intro z
        induction z using QuotientGroup.induction_on with
        | _ e =>
          rw [← QuotientGroup.mk_mul, hBdef, hBdef, hBdef]
          exact hΦAL c₁ c₂ e
  · -- additivity in the second variable
    intro x
    induction x using QuotientGroup.induction_on with
    | _ c =>
      intro y
      induction y using QuotientGroup.induction_on with
      | _ e₁ =>
        intro z
        induction z using QuotientGroup.induction_on with
        | _ e₂ =>
          rw [← QuotientGroup.mk_mul, hBdef, hBdef, hBdef]
          exact hΦAR c e₁ e₂
  · -- non-degeneracy in the first variable
    intro x hx
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
    have hcA : (c : P) ∉ A := by
      intro hc
      refine hx ?_
      rw [QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hc
    have hnc : ¬ (∀ y ∈ E, (c : P) * y * (c : P)⁻¹ * y⁻¹ ∈ Work.Higman.powSub A 2) := by
      intro hall
      exact hcA (radC (c : P) c.2 hall)
    push_neg at hnc
    obtain ⟨y, hy, hyne⟩ := hnc
    refine ⟨QuotientGroup.mk (⟨y, hy⟩ : ↥E), ?_⟩
    rw [hBdef]
    intro hcon
    have hmem : (⟨⁅(c : P), y⁆, hmemA (c : P) c.2 y hy⟩ : ↥A)
        ∈ (Work.Higman.powSub A 2).subgroupOf A := by
      rw [← QuotientGroup.eq_one_iff]
      exact hcon
    have hA2 : ⁅(c : P), y⁆ ∈ Work.Higman.powSub A 2 := Subgroup.mem_subgroupOf.mp hmem
    exact hyne (by rwa [commutatorElement_def] at hA2)
  · -- non-degeneracy in the second variable
    intro y hy
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective y
    have heA : (e : P) ∉ A := by
      intro he
      refine hy ?_
      rw [QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr he
    have hnc : ¬ (∀ x ∈ C, (e : P) * x * (e : P)⁻¹ * x⁻¹ ∈ Work.Higman.powSub A 2) := by
      intro hall
      exact heA (radE (e : P) e.2 hall)
    push_neg at hnc
    obtain ⟨x, hx, hxne⟩ := hnc
    refine ⟨QuotientGroup.mk (⟨x, hx⟩ : ↥C), ?_⟩
    rw [hBdef]
    intro hcon
    have hmem : (⟨⁅(x : P), (e : P)⁆, hmemA (x : P) hx (e : P) e.2⟩ : ↥A)
        ∈ (Work.Higman.powSub A 2).subgroupOf A := by
      rw [← QuotientGroup.eq_one_iff]
      exact hcon
    have hA2 : ⁅(x : P), (e : P)⁆ ∈ Work.Higman.powSub A 2 := Subgroup.mem_subgroupOf.mp hmem
    have hne : ⁅(e : P), (x : P)⁆ ∉ Work.Higman.powSub A 2 := by
      intro hh
      exact hxne (by
        rw [show (e : P) * x * (e : P)⁻¹ * x⁻¹ = ⁅(e : P), (x : P)⁆ by
          rw [commutatorElement_def]]
        exact hh)
    exact hne (by
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ hA2)

end Work.Commutator
