import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.Case2ParityQOf
import Submission.Work.CORE4.Case2ParityIso
import Submission.Work.CORE4.Case2Fill
import Submission.Work.CORE4.Case2KmulS0
import Submission.Work.CORE4.Case2Count11
import Submission.Work.CORE4.ProjOfInfBot

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## The projection of the internal direct product `P ⊔ E`

`P` and `E` commute elementwise and meet in `⊥`, so `P ⊔ E ≅ P × E` and there is a projection
`π : ↥(P ⊔ E) →* ↥E` with kernel `P`.  The lemmas below compute, for a subgroup `X ≤ P ⊔ E`,
the cardinality of `C_{P ⊔ E}(X)` from that of `C_E(π X)`; this is the abstract half of
`Case2CentCard`. -/

section Proj

/-- For the projection `π` onto the `E`-coordinate of the internal direct product `P ⊔ E`, the
element `x * (π x)⁻¹` lies in `P`. -/
theorem proj_mul_inv_mem {P E : Subgroup G}
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) (π : ↥(P ⊔ E) →* ↥E)
    (hπ : ∀ (p : G) (hp : p ∈ P) (e : G) (he : e ∈ E),
      π ⟨p * e, Subgroup.mul_mem_sup hp he⟩ = ⟨e, he⟩) :
    ∀ x : ↥(P ⊔ E), (x : G) * (((π x : ↥E) : G))⁻¹ ∈ P := by
  intro x
  obtain ⟨p, hp, e, he, hpe⟩ := (Work.CORE4.mem_sup_iff_eq_mul hcomm (x : G)).mp x.2
  have hxe : x = ⟨p * e, Subgroup.mul_mem_sup hp he⟩ := Subtype.ext hpe.symm
  have hπx : π x = ⟨e, he⟩ := by rw [hxe]; exact hπ p hp e he
  have hval : ((π x : ↥E) : G) = e := by rw [hπx]
  rw [hval, show (x : G) = p * e from hpe.symm, mul_assoc, mul_inv_cancel, mul_one]
  exact hp

/-- An element of `P` is central in `P ⊔ E` when `P` is commutative and centralizes `E`. -/
theorem mem_sup_central {P E : Subgroup G}
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x)
    (hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    ∀ a ∈ P, ∀ w ∈ (P ⊔ E : Subgroup G), a * w = w * a := by
  intro a ha w hw
  obtain ⟨p, hp, e, he, hpe⟩ := (Work.CORE4.mem_sup_iff_eq_mul hcomm w).mp hw
  calc a * w = a * (p * e) := by rw [hpe]
    _ = (a * p) * e := by rw [mul_assoc]
    _ = (p * a) * e := by rw [hPab a ha p hp]
    _ = p * (a * e) := by rw [mul_assoc]
    _ = p * (e * a) := by rw [hcomm a ha e he]
    _ = w * a := by rw [← hpe, mul_assoc]

/-- Two elements `w, x` of the internal direct product `P ⊔ E` commute **iff** their projections
to `E` commute (the `P`-coordinate being commutative). -/
theorem commute_iff_proj {P E : Subgroup G}
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x)
    (hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (π : ↥(P ⊔ E) →* ↥E)
    (hπ : ∀ (p : G) (hp : p ∈ P) (e : G) (he : e ∈ E),
      π ⟨p * e, Subgroup.mul_mem_sup hp he⟩ = ⟨e, he⟩) :
    ∀ w x : ↥(P ⊔ E),
      ((w : G) * (x : G) = (x : G) * (w : G)) ↔
      (((π w : ↥E) : G) * ((π x : ↥E) : G) = ((π x : ↥E) : G) * ((π w : ↥E) : G)) := by
  intro w x
  have hpz := mem_sup_central hcomm hPab
  have hproj := proj_mul_inv_mem hcomm π hπ
  obtain ⟨aw, hawP, haw⟩ : ∃ aw ∈ P, aw = (w : G) * (((π w : ↥E) : G))⁻¹ := ⟨_, hproj w, rfl⟩
  obtain ⟨ax, haxP, hax⟩ : ∃ ax ∈ P, ax = (x : G) * (((π x : ↥E) : G))⁻¹ := ⟨_, hproj x, rfl⟩
  have hw_eq : (w : G) = aw * ((π w : ↥E) : G) := by rw [haw]; group
  have hx_eq : (x : G) = ax * ((π x : ↥E) : G) := by rw [hax]; group
  have h_ax_piw : ax * ((π w : ↥E) : G) = ((π w : ↥E) : G) * ax :=
    hpz ax haxP ((π w : ↥E) : G) (Subgroup.mem_sup_right (π w).2)
  have hawax : aw * ax = ax * aw := hPab aw hawP ax haxP
  have heq1 : (w : G) * (x : G) =
      (aw * ax) * (((π w : ↥E) : G) * ((π x : ↥E) : G)) := by
    rw [hw_eq, hx_eq]
    calc (aw * ((π w : ↥E) : G)) * (ax * ((π x : ↥E) : G))
        = aw * (((π w : ↥E) : G) * (ax * ((π x : ↥E) : G))) := by group
      _ = aw * ((((π w : ↥E) : G) * ax) * ((π x : ↥E) : G)) := by group
      _ = aw * ((ax * ((π w : ↥E) : G)) * ((π x : ↥E) : G)) := by rw [← h_ax_piw]
      _ = (aw * ax) * (((π w : ↥E) : G) * ((π x : ↥E) : G)) := by group
  have heq2 : (x : G) * (w : G) =
      (aw * ax) * (((π x : ↥E) : G) * ((π w : ↥E) : G)) := by
    rw [hw_eq, hx_eq]
    calc (ax * ((π x : ↥E) : G)) * (aw * ((π w : ↥E) : G))
        = ax * (((π x : ↥E) : G) * (aw * ((π w : ↥E) : G))) := by group
      _ = ax * ((((π x : ↥E) : G) * aw) * ((π w : ↥E) : G)) := by group
      _ = ax * ((aw * ((π x : ↥E) : G)) * ((π w : ↥E) : G)) := by
            rw [show ((π x : ↥E) : G) * aw = aw * ((π x : ↥E) : G) from
              (hpz aw hawP ((π x : ↥E) : G) (Subgroup.mem_sup_right (π x).2)).symm]
      _ = (ax * aw) * (((π x : ↥E) : G) * ((π w : ↥E) : G)) := by group
      _ = (aw * ax) * (((π x : ↥E) : G) * ((π w : ↥E) : G)) := by rw [← hawax]
  rw [heq1, heq2]
  exact mul_left_cancel_iff

/-- The kernel of the projection of `P ⊔ E` onto `E` is `P`. -/
theorem proj_ker {P E : Subgroup G}
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) (π : ↥(P ⊔ E) →* ↥E)
    (hπ : ∀ (p : G) (hp : p ∈ P) (e : G) (he : e ∈ E),
      π ⟨p * e, Subgroup.mul_mem_sup hp he⟩ = ⟨e, he⟩) :
    π.ker = P.subgroupOf (P ⊔ E) := by
  have hproj := proj_mul_inv_mem hcomm π hπ
  ext y
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  constructor
  · intro hy
    have := hproj y
    rw [hy] at this
    simpa using this
  · intro hy
    have hy_eq : y = ⟨(y : G) * 1, Subgroup.mul_mem_sup hy E.one_mem⟩ :=
      Subtype.ext (by simp)
    rw [hy_eq, hπ (y : G) hy 1 E.one_mem]
    exact Subtype.ext rfl

/-- The projection of `P ⊔ E` onto `E` is surjective. -/
theorem proj_surjective {P E : Subgroup G} (π : ↥(P ⊔ E) →* ↥E)
    (hπ : ∀ (p : G) (hp : p ∈ P) (e : G) (he : e ∈ E),
      π ⟨p * e, Subgroup.mul_mem_sup hp he⟩ = ⟨e, he⟩) :
    Function.Surjective π := by
  intro e
  refine ⟨⟨(1 : G) * (e : G), Subgroup.mul_mem_sup P.one_mem e.2⟩, ?_⟩
  rw [hπ 1 P.one_mem (e : G) e.2]

end Proj

/-- **Centralizer in the internal direct product.**  If `P` and `E` commute elementwise, `P` is
commutative and `P ⊓ E = ⊥`, and `π : ↥(P ⊔ E) →* ↥E` is the projection onto `E`, then for every
subgroup `X ≤ P ⊔ E`,
`|C_{P ⊔ E}(X)| = |P| · |C_E(π X)|`.
(Here `C_{P ⊔ E}(X) = C_G(X) ⊓ (P ⊔ E)` and `C_E(π X)` is the centralizer inside `↥E` of the
image of `X` under `π`.) -/
theorem CardCentralizerInfSup {G : Type} [Group G] [Finite G]
    {P E : Subgroup G} (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x)
    (hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hinf : P ⊓ E = ⊥)
    (π : ↥(P ⊔ E) →* ↥E)
    (hπ : ∀ (p : G) (hp : p ∈ P) (e : G) (he : e ∈ E),
      π ⟨p * e, Subgroup.mul_mem_sup hp he⟩ = ⟨e, he⟩)
    (X : Subgroup G) (hX : X ≤ P ⊔ E) :
    Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓ (P ⊔ E)) =
      Nat.card ↥P * Nat.card ↥(Subgroup.centralizer
        ((X.subgroupOf (P ⊔ E)).map π : Set ↥E)) := by
  classical
  have hpz := mem_sup_central hcomm hPab
  have hcommute := commute_iff_proj hcomm hPab π hπ
  have hker := proj_ker hcomm π hπ
  have hsurj := proj_surjective π hπ
  set C : Subgroup G := Subgroup.centralizer (X : Set G) ⊓ (P ⊔ E) with hCdef
  have hCle : C ≤ P ⊔ E := inf_le_right
  let f : ↥C →* ↥E := π.comp (Subgroup.inclusion hCle)
  have hPleC : P ≤ C := by
    refine le_inf ?_ le_sup_left
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hpz a ha x (hX hx)).symm
  have hPker : Nat.card ↥f.ker = Nat.card ↥P := by
    have hfker : f.ker = P.subgroupOf C := by
      ext c
      change π (Subgroup.inclusion hCle c) = 1 ↔ (c : G) ∈ P
      rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
      rfl
    rw [hfker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleC).toEquiv
  have hfrange : f.range = Subgroup.centralizer ((X.subgroupOf (P ⊔ E)).map π : Set ↥E) := by
    ext z
    rw [MonoidHom.mem_range, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨c, rfl⟩
      intro y hy
      obtain ⟨x', hx'mem, rfl⟩ := Subgroup.mem_map.mp hy
      change π x' * π (Subgroup.inclusion hCle c) = π (Subgroup.inclusion hCle c) * π x'
      have hcx : (x' : G) * (c : G) = (c : G) * (x' : G) :=
        Subgroup.mem_centralizer_iff.mp c.2.1 (x' : G) (Subgroup.mem_subgroupOf.mp hx'mem)
      have hp := (hcommute (Subgroup.inclusion hCle c) x').mp hcx.symm
      exact Subtype.ext (by simpa using hp.symm)
    · intro hz
      obtain ⟨w, hw⟩ := hsurj z
      have hwc : (w : G) ∈ C := by
        refine ⟨Subgroup.mem_centralizer_iff.mpr (fun x hx => ?_), w.2⟩
        have hx'' : (⟨x, hX hx⟩ : ↥(P ⊔ E)) ∈ X.subgroupOf (P ⊔ E) :=
          Subgroup.mem_subgroupOf.mpr hx
        have hzy := hz (π ⟨x, hX hx⟩) (Subgroup.mem_map.mpr ⟨⟨x, hX hx⟩, hx'', rfl⟩)
        have hzy' : ((π ⟨x, hX hx⟩ : ↥E) : G) * ((π w : ↥E) : G) =
            ((π w : ↥E) : G) * ((π ⟨x, hX hx⟩ : ↥E) : G) := by
          rw [← hw] at hzy
          exact Subtype.ext_iff.mp hzy
        exact ((hcommute w ⟨x, hX hx⟩).mpr hzy'.symm).symm
      exact ⟨⟨w, hwc⟩, hw⟩
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hPker, hfrange] at hcard
  rw [hCdef] at hcard
  exact hcard.symm

/-! ## Transport of centralizer cardinalities along an isomorphism -/

/-- Centralizers of subgroups have the same cardinality under a group isomorphism. -/
theorem card_centralizer_map_iso {G H : Type} [Group G] [Group H] (ψ : G ≃* H) (Y : Subgroup G) :
    Nat.card ↥(Subgroup.centralizer (Y : Set G)) =
      Nat.card ↥(Subgroup.centralizer ((Y.map ψ.toMonoidHom) : Set H)) := by
  have hmap : (Subgroup.centralizer (Y : Set G)).map ψ.toMonoidHom =
      Subgroup.centralizer ((Y.map ψ.toMonoidHom) : Set H) := by
    refine le_antisymm ?_ ?_
    · have h := Subgroup.map_centralizer_le_centralizer_image (Y : Set G) ψ.toMonoidHom
      rw [Subgroup.coe_map]
      exact h
    · intro x hx
      rw [Subgroup.mem_map]
      refine ⟨ψ.symm x, Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_), by simp⟩
      apply ψ.injective
      simp only [map_mul, ψ.apply_symm_apply]
      exact Subgroup.mem_centralizer_iff.mp hx (ψ y) (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
  rw [← hmap, Subgroup.card_map_of_injective ψ.injective]

/-! ## The centralizer of an odd prime-order subgroup of `PSL(2,q)` -/

/-- In `PSL(2,q)` (`q = pF^kF` odd, `q ≥ 5`), the centralizer of a subgroup `Y` of odd prime order
`r ≠ 2, pF` is cyclic of order `(q + 1)/2` or `(q - 1)/2`; if `r` divides the half `k` of `q ± 1`
then that half is the one, i.e. `|C(Y)| = k`. -/
theorem CardCentralizerPrimePSL2 (I : Work.GW2.C4Inputs) {pF kF r k : ℕ} [Fact pF.Prime]
    (hpFodd : Odd pF) (h5 : 5 ≤ pF ^ kF) (hr : r.Prime) (hr2 : r ≠ 2) (hrpF : r ≠ pF)
    (hk : 2 * k = pF ^ kF + 1 ∨ 2 * k = pF ^ kF - 1) (hrk : r ∣ k)
    (Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))
    (hY : Nat.card Y = r) :
    Nat.card ↥(Subgroup.centralizer
      (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))) = k := by
  obtain ⟨-, hCcard, hNnorm⟩ := I.l2torusNorm pF kF hpFodd h5 r hr hr2 hrpF Y hY
  have hrc : r ∣ Nat.card ↥(Subgroup.centralizer
      (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))) := by
    obtain ⟨ψ⟩ := hNnorm
    have hZ : Nat.card ↥(Subgroup.normalizer
        (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))) =
        2 * Nat.card ↥(Subgroup.centralizer
          (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))) := by
      rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
    have h1 : r ∣ Nat.card ↥(Subgroup.normalizer
        (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))) := by
      rw [← hY]
      exact Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := Y))
    rw [hZ] at h1
    rcases (Nat.Prime.dvd_mul hr).mp h1 with h | h
    · exfalso
      rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h1
      · exact hr.ne_one h1
      · exact hr2 h1
    · exact h
  rcases hCcard with hc | hc <;> rcases hk with hk | hk
  · exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (by rw [hc, hk])
  · exfalso
    have hcd : Nat.card ↥(Subgroup.centralizer
        (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))) = k + 1 := by
      omega
    have hdvd : r ∣ Nat.card ↥(Subgroup.centralizer
        (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))) - k :=
      Nat.dvd_sub hrc hrk
    rw [hcd, Nat.add_sub_cancel_left] at hdvd
    exact hr.not_dvd_one hdvd
  · exfalso
    have hcd : k = Nat.card ↥(Subgroup.centralizer
        (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))) + 1 := by
      omega
    have hdvd : r ∣ k - Nat.card ↥(Subgroup.centralizer
        (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))) :=
      Nat.dvd_sub hrk hrc
    rw [hcd, Nat.add_sub_cancel_left] at hdvd
    exact hr.not_dvd_one hdvd
  · exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (by rw [hc, hk])

/-! ## `Case2CentCard` -/

theorem Case2CentCard (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} (hbc : Work.GW2.BenderCtx G) (h2 : Work.GW2.Case2 B)
    (h : Work.GW2.Case2Ctx B) (hplus : Work.GW2.Case2PrePlus B h.D)
    (h7 : Work.GW2.Case2SevenFacts B h.D) (h8 : Work.GW2.Case2EightAll B h.D)
    (p : ℕ) (P A : Subgroup G) (hpp : p.Prime) (hPF : P ≤ h.D.F)
    (hPcard : Nat.card P = p) (hObj : Work.GW2.Case2EightObj h.D p P A)
    (X : Subgroup G) (hXW : X ≤ P ⊔ Work.GW2.layerIn h.D.M) (hXne : X ≠ P)
    (hXconj : ∃ g : G, X = Work.GW2.conjSub g P) :
    Nat.card ↥(Subgroup.centralizer ((X : Set G)) ⊓ (P ⊔ Work.GW2.layerIn h.D.M)) =
      Nat.card ↥h.D.K * Nat.card ↥B.S0 * p := by
  classical
  set E : Subgroup G := Work.GW2.layerIn h.D.M with hE
  have hXW' : X ≤ P ⊔ E := by rw [hE]; exact hXW
  obtain ⟨pF, kF, hpF, φ, k, k', hpFodd, h7q, hkeven, hk'odd, hdisj, hrel, hCcard⟩ :=
    Case2ParityIso I G hbc B h
  haveI : Fact pF.Prime := hpF
  have hqodd : Odd (pF ^ kF) := hpFodd.pow
  rw [← hE] at hCcard
  have hkK : k = Nat.card ↥h.D.K * Nat.card ↥B.S0 :=
    Case2KmulS0 G I hbc B h (pF ^ kF) k k' hqodd h7q hdisj hrel
  -- `P` centralizes `E`, `P` is commutative, `P ⊓ E = ⊥`
  have hPcomm : ∀ x ∈ P, ∀ y ∈ Work.GW2.layerIn h.D.M, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp
      (Work.GW2.Case2Pre.F_cent B h.D h.pre (hPF hx)) y hy).symm
  have hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    haveI : IsMulCommutative ↥h.D.F := h.F_cyclic.isMulCommutative
    have hFc : h.D.F ≤ Subgroup.centralizer (h.D.F : Set G) := Subgroup.le_centralizer h.D.F
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hFc (hPF hx)) y (hPF hy)).symm
  have hZE : Subgroup.center ↥E = ⊥ := by
    rw [hE]
    exact center_eq_bot_of_mulEquiv φ (center_PSL2_bot pF kF hpFodd (by omega))
  have hPEinf : P ⊓ E = ⊥ :=
    inf_eq_bot_of_le_centralizer
      (fun x hx => Subgroup.mem_centralizer_iff.mpr (fun y hy => (hPcomm x hx y hy).symm)) hZE
  obtain ⟨π, hπ⟩ := ProjOfInfBot P E hPcomm hPEinf
  -- order of `X` and triviality of `X ⊓ P`
  have hXcard : Nat.card ↥X = p := by
    obtain ⟨g, hg⟩ := hXconj
    rw [hg, Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hPcard
  have hXPbot : X ⊓ P = ⊥ := by
    have hdvd : Nat.card ↥(X ⊓ P) ∣ p := by
      rw [← hXcard]; exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hpp).mp hdvd with h1 | hp
    · exact Subgroup.eq_bot_of_card_eq (X ⊓ P) h1
    · exfalso
      have hXP : X ⊓ P = X := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hp, hXcard])
      have hXle : X ≤ P := by rw [← hXP]; exact inf_le_right
      exact hXne (Subgroup.eq_of_le_of_card_ge hXle (by rw [hXcard, hPcard]))
  -- the image `π X` has order `p`
  have hker : π.ker = P.subgroupOf (P ⊔ E) := proj_ker hPcomm π hπ
  have hYcard : Nat.card ↥((X.subgroupOf (P ⊔ E)).map π) = p := by
    have hkey := Subgroup.relIndex_mul_card π.ker (X.subgroupOf (P ⊔ E))
    rw [Subgroup.relIndex_ker] at hkey
    have hkerbot : π.ker ⊓ X.subgroupOf (P ⊔ E) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      rw [Subgroup.mem_inf] at hy
      have hyP : (y : G) ∈ P := by
        have h1 := hy.1
        rw [hker, Subgroup.mem_subgroupOf] at h1
        exact h1
      have hyX : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy.2
      have hmem : (y : G) ∈ X ⊓ P := ⟨hyX, hyP⟩
      rw [hXPbot, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    rw [hkerbot, Subgroup.card_bot, mul_one] at hkey
    calc Nat.card ↥((X.subgroupOf (P ⊔ E)).map π)
        = Nat.card ↥(X.subgroupOf (P ⊔ E)) := hkey
      _ = Nat.card ↥X := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXW').toEquiv
      _ = p := hXcard
  -- the half `k` and the divisibility data
  have hpK0 : p ∣ Nat.card ↥h.D.K := by
    obtain ⟨A', hObjA', hFactsA'⟩ := h8 p P hpp hPF hPcard
    exact dvd_trans hFactsA'.1 (Subgroup.card_dvd_of_le (show h.D.K0 ≤ h.D.K from inf_le_right))
  have hKE : h.D.K ≤ E := by rw [hE]; exact K_le_layerIn_of_case2 h hplus
  have hKsub : h.D.K ≤ E ⊓ B.H :=
    le_inf hKE (le_trans (Work.GW2.Case2Data.K_le_U B h.D) (Work.GW2.BenderSetup.U_le_H B))
  have hpK : p ∣ k := by
    have hp2k : p ∣ 2 * k := by
      have h1 : Nat.card ↥h.D.K ∣ Nat.card ↥(E ⊓ B.H) := Subgroup.card_dvd_of_le hKsub
      rw [hCcard] at h1
      exact dvd_trans hpK0 h1
    rcases (Nat.Prime.dvd_mul hpp).mp hp2k with h1 | h1
    · exfalso
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h2 | h2
      · exact hpp.ne_one h2
      · have h2dvd : 2 ∣ Nat.card ↥B.U := by
          rw [← h2]
          exact dvd_trans hpK0 (Subgroup.card_dvd_of_le (Work.GW2.Case2Data.K_le_U B h.D))
        obtain ⟨m, hm⟩ := h2dvd
        obtain ⟨t, ht⟩ := Work.GW2.BenderSetup.U_odd B
        omega
    · exact h1
  have hkk : 2 * k = pF ^ kF + 1 ∨ 2 * k = pF ^ kF - 1 :=
    hdisj.elim (fun hh => Or.inl hh.1) (fun hh => Or.inr hh.1)
  -- the centralizer inside `E` has order `k`
  have hcentE : Nat.card ↥(Subgroup.centralizer (((X.subgroupOf (P ⊔ E)).map π : Subgroup ↥E)
      : Set ↥E)) = k := by
    rw [card_centralizer_map_iso φ ((X.subgroupOf (P ⊔ E)).map π)]
    refine CardCentralizerPrimePSL2 I hpFodd (by omega) hpp ?_ ?_ hkk hpK
      (Subgroup.map φ.toMonoidHom ((X.subgroupOf (P ⊔ E)).map π)) ?_
    · intro h2
      have h2dvd : 2 ∣ Nat.card ↥B.U := by
        rw [← h2]
        exact dvd_trans hpK0 (Subgroup.card_dvd_of_le (Work.GW2.Case2Data.K_le_U B h.D))
      obtain ⟨m, hm⟩ := h2dvd
      obtain ⟨t, ht⟩ := Work.GW2.BenderSetup.U_odd B
      omega
    · intro heq
      have hkF0 : kF ≠ 0 := by rintro rfl; simp at h7q
      have hdvdq : pF ∣ pF ^ kF := dvd_pow_self pF hkF0
      have hdvdk : pF ∣ k := heq ▸ hpK
      have hdvd2k : pF ∣ 2 * k := dvd_mul_of_dvd_right hdvdk 2
      have hone1 : pF ∣ 1 := by
        rcases hdisj with ⟨h1, -⟩ | ⟨h1, -⟩
        · have h2 : pF ∣ pF ^ kF + 1 := by rw [← h1]; exact hdvd2k
          exact (Nat.dvd_add_iff_right hdvdq).mpr h2
        · have h2 : pF ∣ pF ^ kF - 1 := by rw [← h1]; exact hdvd2k
          have h3 : pF ∣ 1 + (pF ^ kF - 1) := by
            rw [Nat.add_comm, Nat.sub_add_cancel (by omega : 1 ≤ pF ^ kF)]
            exact hdvdq
          exact (Nat.dvd_add_iff_left h2).mpr h3
      have h4 := Nat.le_of_dvd one_pos hone1
      have h5 := hpF.out.two_le
      omega
    · rw [Subgroup.card_map_of_injective φ.injective]
      exact hYcard
  -- assembly
  have hStep1 : Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓ (P ⊔ E)) =
      Nat.card ↥P * Nat.card ↥(Subgroup.centralizer
        (((X.subgroupOf (P ⊔ E)).map π : Subgroup ↥E) : Set ↥E)) :=
    CardCentralizerInfSup hPcomm hPab hPEinf π hπ X hXW'
  rw [hStep1, hPcard, hcentE, hkK]
  ring

end Work.CORE4
