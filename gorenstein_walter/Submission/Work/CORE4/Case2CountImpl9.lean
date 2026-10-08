import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.Defs27
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Arith
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.Case2ParityQOf
import Submission.Work.CORE4.Case2Fill
import Submission.Work.CORE4.Case2KmulS0
import Submission.Work.CORE4.Case2NotInvNormal
import Submission.Work.CORE4.Case2S0_comm_U
import Submission.Work.CORE4.Case2Numeric2
import Submission.Work.CORE4.Case2BGK
import Submission.Work.CORE4.Case2BGData
import Submission.Work.CORE4.Case2NormalizerP
import Submission.Work.CORE4.Case2CountPieces
import Submission.Work.CORE4.Case2Count11
import Submission.Work.CORE4.Case2LowerBound9
import Submission.Work.CORE4.Counting.PerXIntersectBound
import Submission.Work.CORE4.Counting.PerXAmalgamCount
import Submission.Work.CORE4.PerXAssembly
import Submission.Work.CORE4.Counting.EConjLayerIn
import Submission.Work.CORE4.Case2Fibre9
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.Case2PerXBound9
import Submission.Work.CORE4.Case2PerXBound9Corrected

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## 0. Conjugation plumbing

Self-contained copies (so that this module does not depend on the still-`sorry`ed
`Work.CORE4.Counting.PerXNotA`). -/

/-- `(K^g)^{g⁻¹} = K`. -/
theorem conjSub_inv_conjSub9 (g : G) (K : Subgroup G) :
    Work.GW2.conjSub g⁻¹ (Work.GW2.conjSub g K) = K := by
  rw [Work.GW2.conjSub, Work.GW2.conjSub, Subgroup.map_map]
  have h : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply]
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  rw [h, Subgroup.map_id]

/-- `Y ↦ Y^e` is injective on subgroups. -/
theorem conjSub_inj9 (e : G) : Function.Injective fun K : Subgroup G =>
    Work.GW2.conjSub e K := by
  intro K L h
  have h' := congrArg (fun M : Subgroup G => Work.GW2.conjSub e⁻¹ M) h
  simpa only [conjSub_inv_conjSub9] using h'

/-- Conjugation by `e` fixes a subgroup `E` as soon as `e ∈ E`. -/
theorem conjSub_fix_of_mem9 {E : Subgroup G} {e : G} (he : e ∈ E) :
    Work.GW2.conjSub e E = E := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact E.mul_mem (E.mul_mem he hy) (E.inv_mem he)
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨e⁻¹ * x * e, ?_, ?_⟩
    · exact E.mul_mem (E.mul_mem (E.inv_mem he) hx) he
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group

/-- Conjugation transports the relation `A ≤ C_G(B)`. -/
theorem conjSub_le_centralizer_iff9 {A B : Subgroup G} {e : G} :
    A ≤ Subgroup.centralizer (B : Set G) ↔
      Work.GW2.conjSub e A ≤
        Subgroup.centralizer ((Work.GW2.conjSub e B : Subgroup G) : Set G) := by
  constructor
  · intro h x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hc : b * a = a * b := Subgroup.mem_centralizer_iff.mp (h ha) b hb
    calc e * b * e⁻¹ * (e * a * e⁻¹) = e * (b * a) * e⁻¹ := by group
      _ = e * (a * b) * e⁻¹ := by rw [hc]
      _ = e * a * e⁻¹ * (e * b * e⁻¹) := by group
  · intro h x hx
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hxe : (MulAut.conj e) x ∈ Work.GW2.conjSub e A := ⟨x, hx, rfl⟩
    have hbe : (MulAut.conj e) b ∈ Work.GW2.conjSub e B := ⟨b, hb, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp (h hxe) ((MulAut.conj e) b) hbe
    have hc2 : (MulAut.conj e) (b * x) = (MulAut.conj e) (x * b) := by
      rw [map_mul, map_mul]; exact hc
    exact (MulAut.conj e).injective hc2

/-! ## 1. Conjugation covariance of `perXSet` -/

/-- Membership in `perXSet`, unfolded. -/
theorem mem_perXSet_iff9 {P E X Y : Subgroup G} :
    Y ∈ perXSet P E X ↔
      (∃ g : G, Y = Work.GW2.conjSub g P) ∧ X ≤ Subgroup.centralizer (Y : Set G) ∧
        ∀ Z : Subgroup G, Z ≤ P ⊔ E → (∃ g : G, Z = Work.GW2.conjSub g P) →
          Z ≤ Subgroup.centralizer (Y : Set G) → Z = X := Iff.rfl

/-- **Conjugation covariance of `perXSet`.**  If an element `e` fixes `P` and `E`, then
conjugation by `e` carries `perXSet P E X` onto `perXSet P E X^e`. -/
theorem perXSet_conjSub_eq_image9 {P E X : Subgroup G} {e : G}
    (hP : Work.GW2.conjSub e P = P) (hE : Work.GW2.conjSub e E = E) :
    perXSet P E (Work.GW2.conjSub e X) =
      Work.GW2.conjSub e '' perXSet P E X := by
  have hPinv : Work.GW2.conjSub e⁻¹ P = P := by
    have h := congrArg (fun M : Subgroup G => Work.GW2.conjSub e⁻¹ M) hP
    simpa only [conjSub_inv_conjSub9] using h.symm
  have hEinv : Work.GW2.conjSub e⁻¹ E = E := by
    have h := congrArg (fun M : Subgroup G => Work.GW2.conjSub e⁻¹ M) hE
    simpa only [conjSub_inv_conjSub9] using h.symm
  have hsup : Work.GW2.conjSub e (P ⊔ E) = P ⊔ E := by
    rw [Work.CORE4.conjSub_sup', hP, hE]
  have hsupinv : Work.GW2.conjSub e⁻¹ (P ⊔ E) = P ⊔ E := by
    rw [Work.CORE4.conjSub_sup', hPinv, hEinv]
  ext Y
  rw [Set.mem_image]
  constructor
  · intro hY
    refine ⟨Work.GW2.conjSub e⁻¹ Y, ?_, ?_⟩
    · rw [mem_perXSet_iff9] at hY ⊢
      refine ⟨?_, ?_, ?_⟩
      · obtain ⟨g, hg⟩ := hY.1
        exact ⟨e⁻¹ * g, by rw [hg, Work.CORE4.conjSub_mul']⟩
      · rw [conjSub_le_centralizer_iff9, Work.CORE4.conjSub_mul', mul_inv_cancel,
          Work.CORE4.conjSub_one']
        exact hY.2.1
      · intro Z hZ hZc hZY
        have hZ' : Work.GW2.conjSub e Z ≤ P ⊔ E := by
          rw [← hsup]; exact Subgroup.map_mono hZ
        have hZc' : Work.GW2.conjSub e Z ≤ Subgroup.centralizer (Y : Set G) := by
          have h := (conjSub_le_centralizer_iff9 (A := Z) (B := Work.GW2.conjSub e⁻¹ Y)
            (e := e)).mp hZY
          rwa [Work.CORE4.conjSub_mul', mul_inv_cancel, Work.CORE4.conjSub_one'] at h
        have hZ'c : ∃ g : G, Work.GW2.conjSub e Z = Work.GW2.conjSub g P := by
          obtain ⟨g, hg⟩ := hZc
          exact ⟨e * g, by rw [hg, Work.CORE4.conjSub_mul']⟩
        exact conjSub_inj9 e (hY.2.2 (Work.GW2.conjSub e Z) hZ' hZ'c hZc')
    · rw [Work.CORE4.conjSub_mul', mul_inv_cancel, Work.CORE4.conjSub_one']
  · rintro ⟨Z, hZ, rfl⟩
    rw [mem_perXSet_iff9] at hZ ⊢
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨g, hg⟩ := hZ.1
      exact ⟨e * g, by rw [hg, Work.CORE4.conjSub_mul']⟩
    · exact (conjSub_le_centralizer_iff9 (A := X) (B := Z) (e := e)).mp hZ.2.1
    · intro Z' hZ' hZ'c hZ'Y
      have hZ'' : Work.GW2.conjSub e⁻¹ Z' ≤ P ⊔ E := by
        rw [← hsupinv]; exact Subgroup.map_mono hZ'
      have hZ''c : Work.GW2.conjSub e⁻¹ Z' ≤ Subgroup.centralizer (Z : Set G) := by
        have h := (conjSub_le_centralizer_iff9 (A := Z') (B := Work.GW2.conjSub e Z)
          (e := e⁻¹)).mp hZ'Y
        rwa [conjSub_inv_conjSub9] at h
      have hZ''gc : ∃ g : G, Work.GW2.conjSub e⁻¹ Z' = Work.GW2.conjSub g P := by
        obtain ⟨g, hg⟩ := hZ'c
        exact ⟨e⁻¹ * g, by rw [hg, Work.CORE4.conjSub_mul']⟩
      have hconj := hZ.2.2 (Work.GW2.conjSub e⁻¹ Z') hZ'' hZ''gc hZ''c
      rw [← hconj, Work.CORE4.conjSub_mul', mul_inv_cancel, Work.CORE4.conjSub_one']

/-- **`perXSet` has the same cardinality for conjugate data.** -/
theorem perXSet_conjSub_ncard9 {P E X : Subgroup G} {e : G}
    (hP : Work.GW2.conjSub e P = P) (hE : Work.GW2.conjSub e E = E) :
    (perXSet P E (Work.GW2.conjSub e X)).ncard = (perXSet P E X).ncard := by
  rw [perXSet_conjSub_eq_image9 hP hE, Set.ncard_image_of_injective _ (conjSub_inj9 e)]

/-! ## 2. The `E(M)`-transport

Every conjugate `X ≠ P` of `P` inside `W = P ⊔ E(M)` is carried by an element of `E(M)` into the
`(p,p)`-group `A = P ⊔ K_p`: `X` projects to an order-`p` subgroup `Y₀ ≤ E(M)`, and `E(M)`
(Dickson) is transitive on its order-`p` subgroups, so some `e ∈ E(M)` sends `Y₀` to `K_p`.  This
is what makes Bender's `X ≤ A` hypothesis (*"Fix such a conjugate `X`, say `X = P^g ≤ A`"*)
harmless: the remaining conjugates are reached by the internal symmetry `E(M)`, and
`#perXSet P E X` is `E(M)`-invariant (`perXSet_conjSub_ncard9`). -/

/-- **The transport.** -/
theorem exists_conjSub_le_A (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (hbc : Work.GW2.BenderCtx G) (h : Work.GW2.Case2Ctx B) {k k' p : ℕ}
    (hkK : k = Nat.card ↥h.D.K * Nat.card ↥B.S0)
    (hkeven : Even k) (hkodd : Odd k')
    (hcases : (2 * k = qOf h + 1 ∧ 2 * k' = qOf h - 1) ∨
      (2 * k = qOf h - 1 ∧ 2 * k' = qOf h + 1))
    (hp : p.Prime) (hpK0 : p ∣ Nat.card ↥h.D.K0)
    (P A : Subgroup G) (hPF : P ≤ h.D.F) (hPcard : Nat.card P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A)
    (X : Subgroup G) (hXW : X ≤ P ⊔ Work.GW2.layerIn h.D.M) (hXne : X ≠ P)
    (hXc : ∃ g : G, X = Work.GW2.conjSub g P) :
    ∃ e ∈ Work.GW2.layerIn h.D.M, Work.GW2.conjSub e X ≤ A := by
  classical
  set E : Subgroup G := Work.GW2.layerIn h.D.M with hE
  -- ## (a) `W = P ⊔ E` is an internal direct product with `P` abelian and `P ⊓ E = ⊥`
  have hPcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    rw [hE] at hy
    exact (Subgroup.mem_centralizer_iff.mp
      (Work.GW2.Case2Pre.F_cent B h.D h.pre (hPF hx)) y hy).symm
  have hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    haveI : IsMulCommutative ↥h.D.F := h.F_cyclic.isMulCommutative
    have hFc : h.D.F ≤ Subgroup.centralizer (h.D.F : Set G) := Subgroup.le_centralizer h.D.F
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hFc (hPF hx)) y (hPF hy)).symm
  have hcenterE : Subgroup.center ↥E = ⊥ := by
    rw [hE]
    haveI : Fact (nineP h).Prime := ⟨nineP_prime h⟩
    obtain ⟨φ⟩ := nineP_iso h
    exact center_eq_bot_of_mulEquiv φ
      (center_PSL2_bot (nineP h) (nineK h) (nineP_odd h)
        (le_trans (by norm_num : 5 ≤ 7) (nineP_seven h)))
  have hPEinf : P ⊓ E = ⊥ :=
    inf_eq_bot_of_le_centralizer
      (fun x hx => Subgroup.mem_centralizer_iff.mpr (fun y hy => (hPcomm x hx y hy).symm)) hcenterE
  obtain ⟨π, hπ⟩ := ProjOfInfBot P E hPcomm hPEinf
  have hproj : ∀ x : ↥(P ⊔ E), (x : G) * (((π x : ↥E) : G))⁻¹ ∈ P :=
    proj_mul_inv_mem hPcomm π hπ
  -- ## (b) the `E`-coordinate `Y₀` of `X`
  have hXW' : X ≤ P ⊔ E := by rw [hE]; exact hXW
  obtain ⟨hXcard, hXPbot⟩ := Fibre9CardConj hp hPcard hXc hXne
  set Yim : Subgroup G := Subgroup.map E.subtype ((X.subgroupOf (P ⊔ E)).map π) with hYim
  have hYimE : Yim ≤ E := by rw [hYim]; exact Subgroup.map_subtype_le _
  have hYimcard : Nat.card ↥Yim = p := by
    rw [hYim, Fibre9ImageCard (P := P) (E := E) (X := X) π hproj hXW' hXPbot, hXcard]
  have hsupP : P ⊔ Yim = P ⊔ X := by
    rw [hYim]
    exact (Fibre9SupProj (P := P) (E := E) (Y := X) π hproj hXW').symm
  have hXle : X ≤ P ⊔ Yim := by rw [hsupP]; exact le_sup_right
  -- ## (c) `A = P ⊔ Kp` with `Kp = Ω_p(K)`
  have hpF : p ∣ Nat.card ↥h.D.F := by
    rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
  have hpK : p ∣ Nat.card ↥h.D.K := hpK0.trans (Subgroup.card_dvd_of_le inf_le_right)
  obtain ⟨Kp, hKp_le, hKp_card, hKp_omega⟩ :=
    CyclicOmegaPrime h.D.K p h.pre.K_cyclic hp hpK
  obtain ⟨Fp, -, hFp_card, hFp_omega⟩ :=
    CyclicOmegaPrime h.D.F p h.F_cyclic hp hpF
  have hP_le_Fp : P ≤ Fp := fun x hx =>
    (hFp_omega x (hPF hx)).mp (pow_eq_one_of_card_eq hPcard hx)
  have hPFp : P = Fp := Subgroup.eq_of_le_of_card_ge hP_le_Fp (by rw [hFp_card, hPcard])
  have hP_omega : ∀ x ∈ h.D.F, x ^ p = 1 ↔ x ∈ P := by
    intro x hx
    rw [hPFp]
    exact hFp_omega x hx
  obtain ⟨-, -, -, -, huniq⟩ :=
    Case2EightPpSupUnique h.D.F h.D.K P Kp p (F_inf_K_eq_bot_c4 B h.D)
      (F_le_normalizer_K_c4 I B h.D) (F_commute_K_c4 I B h.D h.pre)
      hPF hKp_le hP_omega hKp_omega hPcard hKp_card
  have hAeq : A = P ⊔ Kp := huniq A hObj.2.2.2.1 hObj.2.2.2.2.1 hObj.2.2.2.2.2.1
  have hKpE : Kp ≤ E := by rw [hE]; exact hKp_le.trans (K_le_layerIn B h)
  -- ## (d) `Yim` and `Kp` are `E`-conjugate (Dickson: `E(M) ≅ L₂(q)` is transitive on its
  -- order-`p` subgroups)
  have hpdivk : p ∣ k := by
    rw [hkK]
    exact (hpK0.trans (Subgroup.card_dvd_of_le inf_le_right)).mul_right _
  have hpodd : Odd p :=
    Odd.of_dvd_nat B.U_odd (hpF.trans (Subgroup.card_dvd_of_le (h.D.F_le_U B)))
  haveI : Fact (nineP h).Prime := ⟨nineP_prime h⟩
  obtain ⟨φ⟩ := nineP_iso h
  obtain ⟨e, heE, heEq⟩ :=
    Work.CORE4.Counting.EConjLayerIn I G B h (nineP h) (nineK h) k k' inferInstance φ p
      (nineP_odd h) (le_trans (by norm_num : 5 ≤ 7) (nineP_seven h)) hkeven hkodd hcases
      hp hpodd hpdivk
      Yim Kp (by rw [hE] at hYimE; exact hYimE) (by rw [hE] at hKpE; exact hKpE)
      hYimcard hKp_card
  -- ## (e) conclude
  refine ⟨e, heE, ?_⟩
  have hconjP : Work.GW2.conjSub e P = P := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hc : e * y = y * e :=
        Subgroup.mem_centralizer_iff.mp (Work.GW2.Case2Pre.F_cent B h.D h.pre (hPF hy)) e heE
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      exact hy
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hc : e * x = x * e :=
        Subgroup.mem_centralizer_iff.mp (Work.GW2.Case2Pre.F_cent B h.D h.pre (hPF hx)) e heE
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  calc Work.GW2.conjSub e X
      ≤ Work.GW2.conjSub e (P ⊔ Yim) := Subgroup.map_mono hXle
    _ = Work.GW2.conjSub e P ⊔ Work.GW2.conjSub e Yim := Work.CORE4.conjSub_sup' e P Yim
    _ = P ⊔ Kp := by rw [hconjP, heEq]
    _ ≤ A := by rw [hAeq]



/-- `e ∈ E(M)` commutes with every element of `P ≤ D.F`, hence fixes `P` by conjugation. -/
theorem conjSub_eq_self_of_mem_layerIn {B : Work.GW2.BenderSetup G} (h : Work.GW2.Case2Ctx B)
    {P : Subgroup G} (hPF : P ≤ h.D.F) {e : G} (he : e ∈ Work.GW2.layerIn h.D.M) :
    Work.GW2.conjSub e P = P := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hc : e * y = y * e :=
      Subgroup.mem_centralizer_iff.mp (Work.GW2.Case2Pre.F_cent B h.D h.pre (hPF hy)) e he
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    exact hy
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hc : e * x = x * e :=
      Subgroup.mem_centralizer_iff.mp (Work.GW2.Case2Pre.F_cent B h.D h.pre (hPF hx)) e he
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]

/-! ## 3. The `X ∉ A` case is a consequence of the `X ∈ A` case

`PerXInAProp` (Bender's own case `X ≤ A`) implies the full `PerXProp`, hence also the `X ≰ A` case
`PerXNotAProp` of the workspace.  Route: transport every `X` into `A` along `E(M)`
(`exists_conjSub_le_A`) and use the `E(M)`-invariance of `#perXSet`
(`perXSet_conjSub_ncard9`).  This settles the reviewer's doubt recorded in
`Submission/Work/CORE4/Counting/PerXNotA.lean` (the doubt arises from conjugating the *whole*
configuration, which sends `A` to `A^g`; only the internal symmetry `E(M)`, which fixes `P`, `E`
and `A` setwise, is used here). -/

/-- **`PerXProp` from the `X ≤ A` case.** -/
theorem PerXProp_of_InA (I : Work.GW2.C4Inputs) (hIn : PerXInAProp I) : PerXProp I := by
  intro G _ _ hbc B h k k' p P A hkeven hkodd hcases hkK hp hPF hPcard hObj hqodd hq7 hpK0
    hrelMH X hXW hXne hXc
  obtain ⟨e, heE, heA⟩ :=
    exists_conjSub_le_A I hbc h hkK hkeven hkodd hcases hp hpK0 P A hPF hPcard hObj X hXW hXne hXc
  have hPeq : Work.GW2.conjSub e P = P := conjSub_eq_self_of_mem_layerIn h hPF heE
  have hEeq : Work.GW2.conjSub e (Work.GW2.layerIn h.D.M) = Work.GW2.layerIn h.D.M :=
    conjSub_fix_of_mem9 heE
  obtain ⟨g, hg⟩ := hXc
  have hXe_c : ∃ g' : G, Work.GW2.conjSub e X = Work.GW2.conjSub g' P :=
    ⟨e * g, by rw [hg, ← Work.CORE4.conjSub_mul']⟩
  have hXe_ne : Work.GW2.conjSub e X ≠ P := by
    intro hc
    apply hXne
    have h1 : X = Work.GW2.conjSub e⁻¹ P := by
      have h2 := congrArg (Work.GW2.conjSub e⁻¹) hc
      rwa [conjSub_inv_conjSub9] at h2
    rw [h1, conjSub_eq_self_of_mem_layerIn h hPF (Subgroup.inv_mem _ heE)]
  have hXe_W : Work.GW2.conjSub e X ≤ P ⊔ Work.GW2.layerIn h.D.M := by
    have h1 : Work.GW2.conjSub e X ≤
        Work.GW2.conjSub e (P ⊔ Work.GW2.layerIn h.D.M) :=
      Subgroup.map_mono hXW
    rw [Work.CORE4.conjSub_sup', hPeq, hEeq] at h1
    exact h1
  have hbound := hIn G hbc B h k k' p P A hkeven hkodd hcases hkK hp hPF hPcard hObj hqodd hq7
    hpK0 hrelMH (Work.GW2.conjSub e X) hXe_W hXe_ne heA hXe_c
  rwa [perXSet_conjSub_ncard9 hPeq hEeq] at hbound

/-- **The `X ≰ A` case follows from the `X ≤ A` case.** -/
theorem PerXNotA_of_PerXInA (I : Work.GW2.C4Inputs) (hIn : PerXInAProp I) :
    PerXNotAProp I := by
  intro G _ _ hbc B h k k' p P A hkeven hkodd hcases hkK hp hPF hPcard hObj hqodd hq7 hpK0
    hrelMH X hXW hXne _hXnA hXc
  exact PerXProp_of_InA I hIn G hbc B h k k' p P A hkeven hkodd hcases hkK hp hPF hPcard hObj
    hqodd hq7 hpK0 hrelMH X hXW hXne hXc


/-! ## 4. From the copy-restricted bad count to `PerXProp`

`PerXInAProp` is the `perXSet` form of the count; the two halves of (★) — the `𝓓 ∩ 𝓓^X` part
(`PerXIntersectBound`) and the amalgam part (`PerXAmalgamCount`) — are stated for the *bad* set.
This theorem performs the translation: a bad-count bound for the conjugates `X ≤ A` yields
`PerXProp`, i.e. the count for every conjugate `X` of `P` in `P ⊔ E(M)`. -/

/-- **The p. 227 per-`X` count from the copy-restricted bad count.**

Bender's count is stated for the *bad* set (`Y` commuting with a second member `Z ≠ X` of `𝓓`);
this converts it into the `perXSet` form consumed by `Case2LowerBound9_of_perX`.  It is stated at a
fixed `G` (not as a `∀ G`-implication) precisely so that it can be applied inside the pass-9
assembly, where the §4 (7)/(8) data `Case2SevenFacts`/`Case2EightAll` — which `Case2Ctx` alone does
not yet yield sorry-free — are available as hypotheses. -/
theorem perX_of_badBound (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    {B : Work.GW2.BenderSetup G} (h : Work.GW2.Case2Ctx B) {k k' p : ℕ}
    (hkK : k = Nat.card ↥h.D.K * Nat.card ↥B.S0)
    (hkeven : Even k) (hkodd : Odd k')
    (hcases : (2 * k = qOf h + 1 ∧ 2 * k' = qOf h - 1) ∨
      (2 * k = qOf h - 1 ∧ 2 * k' = qOf h + 1))
    (hqodd : Odd (qOf h)) (hq7 : 7 ≤ qOf h)
    (hp : p.Prime) (hpK0 : p ∣ Nat.card ↥h.D.K0)
    (hrelMH : (h.D.M ⊓ B.H).relIndex h.D.M = qOf h * k')
    (P A : Subgroup G) (hPF : P ≤ h.D.F) (hPcard : Nat.card P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A)
    (hbadXA : ∀ g : G, Work.GW2.conjSub g P ≠ P → Work.GW2.conjSub g P ≤ A →
        {Y : Subgroup G | (∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M),
              Y = Work.GW2.conjSub g Z) ∧
            Y ≠ Work.GW2.conjSub g P ∧
            ∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M),
              Z ≠ Work.GW2.conjSub g P ∧ Y ≤ Subgroup.centralizer (Z : Set G)}.ncard ≤
          (Work.GW2.Case2EightP1 P A - 1) + ((qOf h - 1) * qOf h) / p) :
    ∀ X : Subgroup G, X ≤ P ⊔ Work.GW2.layerIn h.D.M → X ≠ P →
      (∃ g : G, X = Work.GW2.conjSub g P) →
      ((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
          (((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) - 1) -
        ((qOf h : ℚ) - 1) * qOf h / (p : ℚ) ≤
      ((perXSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ) := by
  classical
  set E : Subgroup G := Work.GW2.layerIn h.D.M with hE
  set r : ℕ := (h.D.M ⊓ B.H).relIndex h.D.M with hrdef
  -- §4 (11): `|𝓓| = (p₁ − 1) r + 1`
  have h11 : (inConjSet P E).ncard = (Work.GW2.Case2EightP1 P A - 1) * r + 1 := by
    have h111 := Work.CORE4.Counting.Count11Ctx I G hbc B h k k' p P A hkeven hkodd hcases hkK
      hp hPF hPcard hObj hqodd hq7 hpK0 hrelMH
    have hEq : inConjSet P E = {X : Subgroup G | X ≤ P ⊔ Work.GW2.layerIn h.D.M ∧
        ∃ g : G, X = Work.GW2.conjSub g P} := by
      ext Y
      simp only [inConjSet, Set.mem_setOf_eq, hE]
    rw [hEq, hrdef]
    exact h111
  -- ## the per-`X` bound for `X ≤ A`
  have hPerXA : ∀ X : Subgroup G, X ≤ P ⊔ E → X ≠ P → X ≤ A →
      (∃ g : G, X = Work.GW2.conjSub g P) →
      ((Work.GW2.Case2EightP1 P A : ℚ) - 1) * ((r : ℚ) - 1) -
        ((qOf h : ℚ) - 1) * qOf h / (p : ℚ) ≤ ((perXSet P E X).ncard : ℚ) := by
    intro X hXE hXne hXA hXc
    obtain ⟨g, rfl⟩ := hXc
    set Ds : Set (Subgroup G) := inConjSet P E with hDs
    set Dg : Set (Subgroup G) := Work.GW2.conjSub g '' Ds with hDg
    set badC : Set (Subgroup G) :=
      {Y : Subgroup G | (∃ Z ∈ Ds, Y = Work.GW2.conjSub g Z) ∧
        Y ≠ Work.GW2.conjSub g P ∧
        ∃ Z ∈ Ds, Z ≠ Work.GW2.conjSub g P ∧ Y ≤ Subgroup.centralizer (Z : Set G)} with hbadC
    have hDgcard : Dg.ncard = (Work.GW2.Case2EightP1 P A - 1) * r + 1 := by
      rw [hDg, Set.ncard_image_of_injective Ds (conjSub_inj9 g), hDs]
      exact h11
    have hXmem : Work.GW2.conjSub g P ∈ Dg := by
      rw [hDg]
      refine ⟨P, ?_, rfl⟩
      rw [hDs, hE]
      exact ⟨le_sup_left, ⟨1, (Work.CORE4.conjSub_one' P).symm⟩⟩
    have hbadC_le : badC.ncard ≤
        (Work.GW2.Case2EightP1 P A - 1) + ((qOf h - 1) * qOf h) / p := by
      have hh : badC = {Y : Subgroup G |
          ((∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M), Y = Work.GW2.conjSub g Z) ∧
            Y ≠ Work.GW2.conjSub g P ∧
            ∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M),
              Z ≠ Work.GW2.conjSub g P ∧ Y ≤ Subgroup.centralizer (Z : Set G))} := by
        rw [hbadC, hDs, hE]
      rw [hh]
      exact hbadXA g hXne hXA
    -- an element of the copy which is not bad has `X` as its only conjugate in `C_W(·)`
    have hsub : Dg \ {Work.GW2.conjSub g P} ⊆
        perXSet P E (Work.GW2.conjSub g P) ∪ badC := by
      intro Y hY
      rw [Set.mem_sdiff, Set.mem_singleton_iff] at hY
      obtain ⟨hYDg, hYne⟩ := hY
      rw [hDg, Set.mem_image] at hYDg
      obtain ⟨Z₀, hZ₀, hYZ₀⟩ := hYDg
      by_cases hb : ∃ Z ∈ Ds, Z ≠ Work.GW2.conjSub g P ∧
          Y ≤ Subgroup.centralizer (Z : Set G)
      · refine Or.inr ⟨?_, hYne, hb⟩
        exact ⟨Z₀, hZ₀, hYZ₀.symm⟩
      · refine Or.inl ⟨?_, ?_, ?_⟩
        · rw [hDs, hE, inConjSet] at hZ₀
          obtain ⟨-, u, hu⟩ := hZ₀
          exact ⟨g * u, by rw [← hYZ₀, hu, Work.CORE4.conjSub_mul']⟩
        · rw [hDs, hE, inConjSet] at hZ₀
          obtain ⟨hZ₀le, -⟩ := hZ₀
          have hZ₀P : Z₀ ≤ Subgroup.centralizer (P : Set G) :=
            hZ₀le.trans (sup_le_centralizer_P h hPF)
          have hPZ₀ : P ≤ Subgroup.centralizer (Z₀ : Set G) :=
            le_centralizer_comm.mp hZ₀P
          have := conjSub_le_centralizer g hPZ₀
          rwa [← hYZ₀]
        · intro Z hZle hZc hZY
          by_contra hZX
          exact hb ⟨Z, by rw [hDs, hE]; exact ⟨hZle, hZc⟩, hZX,
            le_centralizer_comm.mp hZY⟩
    have hcard_sdiff : (Dg \ {Work.GW2.conjSub g P}).ncard = Dg.ncard - 1 := by
      rw [Set.ncard_sdiff (t := Dg) (by rw [Set.singleton_subset_iff]; exact hXmem),
        Set.ncard_singleton]
    have hle : (Dg \ {Work.GW2.conjSub g P}).ncard ≤
        (perXSet P E (Work.GW2.conjSub g P)).ncard + badC.ncard :=
      (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)
    have hp1 : (1 : ℕ) ≤ Work.GW2.Case2EightP1 P A :=
      Case2EightP1_pos (P := P) (A := A) hObj.2.2.2.2.2.2.1
    have hDgpos : (1 : ℕ) ≤ Dg.ncard :=
      Nat.succ_le_iff.mpr (Set.ncard_pos (Set.toFinite _) |>.mpr ⟨_, hXmem⟩)
    have hdiffcast : (((Dg \ {Work.GW2.conjSub g P}).ncard : ℕ) : ℚ) = (Dg.ncard : ℚ) - 1 := by
      rw [hcard_sdiff, Nat.cast_sub hDgpos, Nat.cast_one]
    have hDgcast : (Dg.ncard : ℚ) = ((Work.GW2.Case2EightP1 P A : ℚ) - 1) * (r : ℚ) + 1 := by
      rw [hDgcard, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_one]
    have hunion : (((Dg \ {Work.GW2.conjSub g P}).ncard : ℕ) : ℚ) ≤
        (((perXSet P E (Work.GW2.conjSub g P)).ncard : ℕ) : ℚ) + ((badC.ncard : ℕ) : ℚ) := by
      exact_mod_cast hle
    have hbadcast : ((badC.ncard : ℕ) : ℚ) ≤
        ((Work.GW2.Case2EightP1 P A : ℚ) - 1) + ((((qOf h - 1) * qOf h) / p : ℕ) : ℚ) := by
      have h1 : ((badC.ncard : ℕ) : ℚ) ≤
          (((Work.GW2.Case2EightP1 P A - 1) + ((qOf h - 1) * qOf h) / p : ℕ) : ℚ) := by
        exact_mod_cast hbadC_le
      rwa [Nat.cast_add, Nat.cast_sub hp1] at h1
    have htdiv : ((((qOf h - 1) * qOf h) / p : ℕ) : ℚ) ≤
        ((qOf h : ℚ) - 1) * (qOf h : ℚ) / (p : ℚ) := by
      have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.pos
      rw [le_div_iff₀ hp0]
      have h1 : ((((qOf h - 1) * qOf h) / p : ℕ) : ℚ) * (p : ℚ) ≤
          (((qOf h - 1) * qOf h : ℕ) : ℚ) := by
        rw [← Nat.cast_mul]
        exact_mod_cast Nat.div_mul_le_self ((qOf h - 1) * qOf h) p
      have h2 : (((qOf h - 1) * qOf h : ℕ) : ℚ) = ((qOf h : ℚ) - 1) * (qOf h : ℚ) := by
        rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ qOf h by have := nineP_seven h; omega),
          Nat.cast_one]
      linarith [h1, h2.le, h2.ge]
    have hgoal : ((Work.GW2.Case2EightP1 P A : ℚ) - 1) * ((r : ℚ) - 1) -
        ((qOf h : ℚ) - 1) * (qOf h : ℚ) / (p : ℚ) ≤
        ((perXSet P E (Work.GW2.conjSub g P)).ncard : ℚ) := by
      nlinarith [hunion, hdiffcast, hDgcast, hbadcast, htdiv]
    simpa using hgoal
  -- ## transport to all `X`
  intro X hXE hXne hXc
  obtain ⟨e, heE, heA⟩ :=
    exists_conjSub_le_A I hbc h hkK hkeven hkodd hcases hp hpK0 P A hPF hPcard hObj X hXE hXne hXc
  have hPeq : Work.GW2.conjSub e P = P := conjSub_eq_self_of_mem_layerIn h hPF heE
  have hEeq : Work.GW2.conjSub e E = E := conjSub_fix_of_mem9 heE
  obtain ⟨g, hg⟩ := hXc
  have hXe_c : ∃ g' : G, Work.GW2.conjSub e X = Work.GW2.conjSub g' P :=
    ⟨e * g, by rw [hg, ← Work.CORE4.conjSub_mul']⟩
  have hXe_ne : Work.GW2.conjSub e X ≠ P := by
    intro hc
    apply hXne
    have h1 : X = Work.GW2.conjSub e⁻¹ P := by
      have h2 := congrArg (Work.GW2.conjSub e⁻¹) hc
      rwa [conjSub_inv_conjSub9] at h2
    rw [h1, conjSub_eq_self_of_mem_layerIn h hPF (Subgroup.inv_mem _ heE)]
  have hXe_E : Work.GW2.conjSub e X ≤ P ⊔ E := by
    have h1 : Work.GW2.conjSub e X ≤ Work.GW2.conjSub e (P ⊔ E) := Subgroup.map_mono hXE
    rw [Work.CORE4.conjSub_sup', hPeq, hEeq] at h1
    exact h1
  have hbound := hPerXA (Work.GW2.conjSub e X) hXe_E hXe_ne heA hXe_c
  rwa [perXSet_conjSub_ncard9 hPeq hEeq] at hbound

/-! ## Bender 1981, §4: the elimination of Case 2

**STATUS (session 5).**  The assembly below is complete modulo exactly one lemma, the p. 227
per-conjugate count in Bender's own case,

    `Work.CORE4.Counting.PerXInA`  (`= PerXInAProp`, `Submission/Work/CORE4/Counting/PerXInA.lean`),

i.e. for every conjugate `X ≠ P` of `P` with `X ≤ A` (Bender's *"Fix such a conjugate `X`, say
`X = P^g ≤ A`"*):

    (p₁ − 1)(qk' − 1) − ((q − 1)/p) q  ≤  #(perXSet P E X).

**What this session added.**  The old route (`Work.CORE4.Case2LowerBoundImpl9`, no longer imported)
rested on the `hBadBound` of `Case2PerXBound9'`, bounding `badSet P E X` over **all** conjugates of
`P`; that hypothesis is *false* (`#{Y ~ P : Y ≤ C_G(A)} ≥ |𝓓| = (p₁−1)qk' + 1 > p₁ + (q−1)q/p`).
The assembly has now been rewired to the correct route: `Case2LowerBound9_of_perX` (§4 (11) + the
per-`X` count ⟹ §4 (12)) fed with `PerXProp_of_InA` (this file), which derives the per-`X` count
for **all** `X` from the `X ≤ A` case by the internal symmetry `E(M)`:

* `exists_conjSub_le_A` — every conjugate `X ≠ P` of `P` inside `W = P ⊔ E(M)` is carried by some
  `e ∈ E(M)` into `A = P ⊔ Ω_p(K)`: the projection of `X` to `E(M)` is an order-`p` subgroup of the
  `L₂(q)`-group `E(M)`, on whose order-`p` subgroups `E(M)` is transitive (`EConjLayerIn`);
* `perXSet_conjSub_ncard9` — `#perXSet` is `E(M)`-invariant (conjugation covariance of `perXSet`),
  because `e ∈ E(M)` fixes `P` (`P ≤ C_G(E(M))`) and `E(M)` itself.

With these two, `PerXNotAProp` (`X ≰ A`) is a *theorem*, not a separate leaf: this settles the doubt
recorded in `Submission/Work/CORE4/Counting/PerXNotA.lean`, which arose from conjugating the *whole*
configuration (sending `A` to `A^g`); only the internal symmetry `E(M)`, which fixes `P`, `E(M)` and
`A` **setwise**, is used.  The whole of §4 (12) therefore rests on **one** true statement,
`PerXInAProp`.

The §4 (9) preliminaries used below (`E(M) ≅ L₂(q)`, `S ≤ E(M)`, `S₀ = C_S(U)`, `k = |K||S₀|`,
`|M : M ⊓ H| = qk'`), §4 (10) (`Case2BGK` + `Case2UpperBoundImpl_proof`), §4 (11) (`Case2Count11`)
and the final ℚ-bookkeeping with `Work.GW2.case2Arith` are all proved. -/

/-- Bender §4 (2) together with `S ≤ E(M)`: `B₀ = C_{U⊓M}(S ⊓ E(M)) = C_{U⊓M}(S)`, hence
`B₀ ≤ C_G(S)`. -/
theorem Case2B0_le_cent_S (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (h : Work.GW2.Case2Ctx B) (hplus : Work.GW2.Case2PrePlus B h.D) :
    h.D.B0 ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G) := by
  have hSinf : ((B.S : Subgroup G) ⊓ Work.GW2.layerIn h.D.M : Subgroup G) = B.S :=
    inf_eq_left.mpr (Work.CORE4.nineP_le (B := B) h)
  have h1 : h.D.B0 ≤ Subgroup.centralizer
      ((((B.S : Subgroup G)) ⊓ Work.GW2.layerIn h.D.M : Subgroup G) : Set G) :=
    (le_of_eq hplus.2.2).trans inf_le_right
  rwa [hSinf] at h1

/-- **Bender §4 (7)--(12)**: the pass-9 leaf `Work.GW2.Case2CountImpl9`, from the §4 (12) amalgam
count `Work.GW2.C27.PerXAmalgamCountProp` as an explicit hypothesis (design pass 27, CORE4 owner
item 4: the body is unchanged, but the one application of the `sorry`-backed
`Work.CORE4.Counting.PerXAmalgamCount` is now the parameter `hAm`).

The conclusion is unsatisfiable (`Work.GW2.case2Arith`), so the proof derives `False` from the §4
configuration.  For the unconditional form, supply
`hAm := Work.GW2.C27.perXAmalgamCount_of_design27 I hL2` (`hL2 : L2pLocalProp`) or the proved
`Work.CORE4.Counting.PerXAmalgamCount` once it is discharged. -/
theorem Case2CountImpl9_of_amalgam (I : Work.GW2.C4Inputs)
    (hAm : Work.GW2.C27.PerXAmalgamCountProp I) : Work.GW2.Case2CountImpl9 I := by
  intro G _ _ hbc B h2 h hplus h7 h8
  classical
  -- §4 (9)/p. 227: `S₀ = O₂(H ⊓ E) = O₂(H) = C_S(U)`, hence `[S₀, U] = ⊥`.
  have hS0comm : ⁅B.S0, B.U⁆ = ⊥ := Case2S0_comm_U I hbc h2 h hplus h7
  have hS0cen : B.S0 ≤ Subgroup.centralizer ((B.U : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hS0comm
  -- Bender's exceptional clause of (8) does not occur (Lemma 2.8 = `I.lem28`).
  have hNotInv : ¬ Work.GW2.Case2InvNormal B h.D :=
    Case2NotInvNormal G I hbc B h hS0cen
  -- The objects of p. 225: `p := |F|.minFac` (a prime) and `P ≤ F` of order `p`.
  obtain ⟨hpprime, -, P, hPF, hPcard⟩ := Case2Fill G B h
  obtain ⟨A, hObj, hFacts⟩ := h8 (Nat.card ↥h.D.F).minFac P hpprime hPF hPcard
  -- §4 (10) parity data with the canonical field order `q = qOf h`; §4 (9) `k = |K|·|S₀|`.
  obtain ⟨k, k', hqodd, hq7, hkeven, hk'odd, hcases, hrelMH⟩ :=
    Case2ParityQOf G I hbc B h
  have hkK : k = Nat.card ↥h.D.K * Nat.card ↥B.S0 :=
    Case2KmulS0 G I hbc B h (qOf h) k k' hqodd hq7 hcases hrelMH
  -- §4 (2) with `S ≤ E(M)`: `B₀ ≤ C_G(S)`.
  have hB0S : h.D.B0 ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G) :=
    Case2B0_le_cent_S I h hplus
  -- the numerical objects of p. 225
  obtain ⟨hpK0, hAleK0, hNP, hNPA, hp0odd, hp0p1, hp1le, hp0p, hrelU, hdisj⟩ := hFacts
  have hpK : (Nat.card ↥h.D.F).minFac ∣ Nat.card ↥h.D.K :=
    dvd_trans hpK0 (Subgroup.card_dvd_of_le inf_le_right)
  have h2p : 2 * (Nat.card ↥h.D.F).minFac ≤ k :=
    Case2N2_two_p_le_k B h hkK hpK
  have hu1 : 1 ≤ Work.GW2.Case2EightU B A := Case2N2_one_le_u B A
  have hup : Work.GW2.Case2EightU B A ≤ (Nat.card ↥h.D.F).minFac :=
    (hdisj.resolve_left hNotInv).1
  have hp03 : 3 ≤ Work.GW2.Case2EightP0 B P A :=
    (hdisj.resolve_left hNotInv).2.2 (Case2N2_not_U_le_M I B h)
  have hHrel : (h.D.M ⊓ B.H).relIndex B.H =
      Work.GW2.Case2EightU B A * Work.GW2.Case2EightP0 B P A :=
    Case2N2_MH_relIndex I B h hNP hNPA
  -- §4 (10): `q k' |G : M| < 6 k² u³ p₀³`, from Theorem A of Bender--Glauberman.
  obtain ⟨D, hDS, hDS0, hDt, hDk⟩ :=
    Case2BGK G I hbc B h k (Work.GW2.Case2EightU B A) (Work.GW2.Case2EightP0 B P A)
      hkK hHrel hB0S
  have h10 := Case2UpperBoundImpl_proof I G hbc B h (qOf h) k k'
    (Work.GW2.Case2EightU B A) (Work.GW2.Case2EightP0 B P A) D hDS hDS0 hDt hDk
    hqodd hq7 hkeven hrelMH hHrel hu1 hp03
  -- §4 (11): `P × E(M)` contains `(p₁ − 1) q k'` conjugates of `P` other than `P`.
  have hCount11 := Case2Count11 I hbc h2 h hplus h7 h8 (Nat.card ↥h.D.F).minFac P A
    hpprime hPF hPcard hObj
  -- §4 (12): Bender's p. 227 lower bound for `|G : M| = |G : N_G(P)|`.  The p. 227
  -- per-conjugate count is supplied in its two halves — `PerXIntersectBound` (the `𝓓 ∩ 𝓓^X` part,
  -- `≤ p₁ − 1`) and `PerXAmalgamCount` (Bender's amalgam count, `≤ (q − 1)q/p`) — at Bender's own
  -- case `X ≤ A`; their union is the bad set of `X` inside the copy `𝓓^X`, and
  -- `perX_of_badBound` (this file) converts the resulting bound into the `perXSet` form for
  -- *all* conjugates `X`, using the internal symmetry `E(M)`.  (The `X ≰ A` case is therefore not
  -- a separate leaf: `PerXProp_of_InA` / `PerXNotA_of_PerXInA`.)
  have hbadXA : ∀ g : G, Work.GW2.conjSub g P ≠ P → Work.GW2.conjSub g P ≤ A →
      {Y : Subgroup G | (∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M),
            Y = Work.GW2.conjSub g Z) ∧
          Y ≠ Work.GW2.conjSub g P ∧
          ∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M),
            Z ≠ Work.GW2.conjSub g P ∧ Y ≤ Subgroup.centralizer (Z : Set G)}.ncard ≤
        (Work.GW2.Case2EightP1 P A - 1) + ((qOf h - 1) * qOf h) / (Nat.card ↥h.D.F).minFac := by
    intro g hg hgA
    set Ds : Set (Subgroup G) := inConjSet P (Work.GW2.layerIn h.D.M) with hDs
    set badg : Set (Subgroup G) :=
      {Y : Subgroup G | (∃ Z ∈ Ds, Y = Work.GW2.conjSub g Z) ∧
        Y ≠ Work.GW2.conjSub g P ∧ ∃ Z ∈ Ds, Z ≠ Work.GW2.conjSub g P ∧
          Y ≤ Subgroup.centralizer (Z : Set G)} with hbadg
    set SI : Set (Subgroup G) :=
      {Y : Subgroup G | Y ∈ Ds ∧ Y ∈ Work.GW2.conjSub g '' Ds ∧ Y ≠ Work.GW2.conjSub g P}
      with hSI
    set SII : Set (Subgroup G) :=
      {Y : Subgroup G | (∃ Z ∈ Ds, Y = Work.GW2.conjSub g Z) ∧ Y ∉ Ds ∧
        ∃ Z ∈ Ds, Z ≠ Work.GW2.conjSub g P ∧ Y ≤ Subgroup.centralizer (Z : Set G)}
      with hSII
    have hsub2 : badg ⊆ SI ∪ SII := by
      intro Y hY
      rw [hbadg, Set.mem_setOf_eq] at hY
      obtain ⟨h1, h2, h3⟩ := hY
      by_cases hYd : Y ∈ Ds
      · refine Or.inl ?_
        rw [hSI, Set.mem_setOf_eq]
        obtain ⟨Z, hZ, hYZ⟩ := h1
        exact ⟨hYd, ⟨Z, hZ, hYZ.symm⟩, h2⟩
      · refine Or.inr ?_
        rw [hSII, Set.mem_setOf_eq]
        exact ⟨h1, hYd, h3⟩
    have hcard2 : badg.ncard ≤ SI.ncard + SII.ncard :=
      (Set.ncard_le_ncard hsub2 (Set.toFinite _)).trans (Set.ncard_union_le _ _)
    have hIcard : SI.ncard ≤ Work.GW2.Case2EightP1 P A - 1 := by
      have h := Work.CORE4.Counting.PerXIntersectBound I G hbc B h k k'
        (Nat.card ↥h.D.F).minFac P A hkeven hk'odd hcases hkK hpprime hPF hPcard hObj g hg hgA
      rw [hSI, hDs]
      exact h
    have hIIcard : SII.ncard ≤
        ((qOf h - 1) * qOf h) / (Nat.card ↥h.D.F).minFac := by
      have h := hAm G hbc B h h2 hplus h7 h8
        (Nat.card ↥h.D.F).minFac P A hpprime hPF hPcard hObj hCount11 g hg hgA
      rw [hSII, hDs]
      exact h
    exact le_trans hcard2 (by omega)
  have hPerX : ∀ X : Subgroup G, X ≤ P ⊔ Work.GW2.layerIn h.D.M → X ≠ P →
      (∃ g : G, X = Work.GW2.conjSub g P) →
      ((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
          (((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) - 1) -
        ((qOf h : ℚ) - 1) * qOf h / (Nat.card ↥h.D.F).minFac ≤
      ((perXSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ) :=
    perX_of_badBound I hbc h hkK hkeven hk'odd hcases hqodd hq7 hpprime hpK0 hrelMH
      P A hPF hPcard hObj hbadXA
  have h12 := Case2LowerBound9_of_perX I hbc h2 h hplus h7 h8 (Nat.card ↥h.D.F).minFac P A
    hpprime hPF hPcard hObj hCount11 hPerX
  -- multiply (12) by `q k' ≥ 0` and compare with (10)
  have hp1ge : 1 ≤ Work.GW2.Case2EightP1 P A := by
    have h3 : 3 ≤ Work.GW2.Case2EightP1 P A := le_trans hp03 hp0p1
    omega
  -- normalise the `ℕ`-casts appearing in (10) and (12)
  have hAqeq : ((qOf h * k' : ℕ) : ℚ) = (qOf h : ℚ) * (k' : ℚ) := by push_cast; ring
  have hAqeq2 : ((qOf h * k' * h.D.M.index : ℕ) : ℚ) =
      (qOf h : ℚ) * (k' : ℚ) * (h.D.M.index : ℚ) := by push_cast; ring
  rw [hrelMH, hAqeq] at h12
  rw [hAqeq2] at h10
  have hqk' : (0 : ℚ) ≤ (qOf h : ℚ) * (k' : ℚ) := by positivity
  have hbound := lt_of_le_of_lt (mul_le_mul_of_nonneg_left h12 hqk') h10
  -- the comparison is Bender's (12), whose negation is `Work.GW2.case2Arith`
  have hle : (((qOf h * k' * (Work.GW2.Case2EightP1 P A - 1) * (qOf h * k')) : ℚ) *
      (((Work.GW2.Case2EightP1 P A : ℚ) - 1) * ((qOf h : ℚ) * (k' : ℚ) - 1) -
        ((qOf h : ℚ) - 1) * (qOf h : ℚ) / (Nat.card ↥h.D.F).minFac)) ≤
      6 * (k : ℚ) ^ 2 * (Work.GW2.Case2EightU B A : ℚ) ^ 3 *
        (Work.GW2.Case2EightP0 B P A : ℚ) ^ 3 := by
    push_cast
    nlinarith [hbound]
  -- `case2Arith` rules out the tuple
  exact (Work.GW2.case2Arith (qOf h) k k' (Nat.card ↥h.D.F).minFac
    (Work.GW2.Case2EightP0 B P A) (Work.GW2.Case2EightP1 P A) (Work.GW2.Case2EightU B A)
    hq7 hqodd hcases hkeven hpprime hp03 hp0odd hp0p1 hp1le hp0p h2p hu1 hup hle).elim

end Work.CORE4
