import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.L2F.Dihedral.dihedral_oddSubgroup
import Submission.Work.L2F.Torus.normalizer_map_eq_of_le_ker
import Submission.Work.CORE4.DihedralConjCentralizerOdd
import Submission.Work.CORE4.NormalizerZpowersDiv
import Submission.Work.CORE4.CardZpowersDiv

namespace Work.CORE4

/-- **Odd-order subgroups of the centralizer of an involution in `L₂(q)`.**

Let `G ≃* PSL(2, q)` with `q = p ^ k`, `p` odd, `q ≥ 5`.  Let `τ ∈ G` be an involution and
`A ≤ C_G(τ)` a subgroup of odd order.  Then `A` is cyclic, and every element of `N_G(A)`
acts on `A` either trivially or by inversion.

Route (mirroring the structure input of Gorenstein–Walter / Bender §4):
* `C_{PSL(2,q)}(τ)` is dihedral of order `q ± 1` (`l2cent`), and an odd-order subgroup of a
  dihedral group is cyclic (`Work.L2F.Dihedral.dihedral_oddSubgroup`), giving cyclicity of `A`.
* For the action, `A` is cyclic of odd order, so it has a unique subgroup of order `r` for each
  prime `r ∣ |A|`; `r ≠ p` because `|A| ∣ q ± 1`.  The torus normalizer `l2torusNorm` attaches to
  this order-`r` subgroup a dihedral normalizer `N ≅ Dihedral(m)` whose rotation subgroup is the
  cyclic centralizer `C`, and every element of `N` acts on `C` by `± 1`
  (`Work.CORE4.DihedralConjCentralizerOdd`).  Since `A ≤ C` and `N_G(A) ≤ N`, all of `N_G(A)`
  acts on `A` by `± 1`. -/
theorem CoreL2OddCentralizer
    (l2cent : Work.GW2.L2InvolutionCentralizerProp)
    (l2torusNorm : Work.GW2.L2TorusNormalizerProp)
    (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hk : 5 ≤ p ^ k)
    (G : Type) [Group G] [Finite G]
    (φ : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))
    (τ : G) (hτ : orderOf τ = 2)
    (A : Subgroup G) (hA : A ≤ Subgroup.centralizer ({τ} : Set G))
    (hodd : Odd (Nat.card A)) :
    IsCyclic A ∧ ∀ g ∈ Subgroup.normalizer (A : Set G), ∀ a ∈ A,
      g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a⁻¹ := by
  haveI : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) := inferInstance
  have hτφ : orderOf (φ τ) = 2 := (orderOf_injective φ.toMonoidHom φ.injective τ).trans hτ
  -- Part 1: cyclicity
  set Ct : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
    Subgroup.centralizer ({φ τ} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) with hCt
  set B : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
    A.map φ.toMonoidHom with hB
  have hBcard : Nat.card B = Nat.card A := Subgroup.card_map_of_injective φ.injective
  have hBodd : Odd (Nat.card B) := by rw [hBcard]; exact hodd
  have hBle : B ≤ Ct := by
    intro b hb
    rw [hCt, Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [hB] at hb
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
    have hcomm : τ * a = a * τ := by
      have h := hA ha
      rw [Subgroup.mem_centralizer_iff] at h
      exact h τ (Set.mem_singleton τ)
    have h2 : φ.toMonoidHom (τ * a) = φ.toMonoidHom (a * τ) := by rw [hcomm]
    rw [map_mul, map_mul] at h2
    exact h2
  obtain ⟨n, hn, ⟨e0⟩⟩ := l2cent p k hp hk (φ τ) hτφ
  set Bct : Subgroup ↥Ct := B.subgroupOf Ct with hBct
  set Bn : Subgroup (DihedralGroup n) := Bct.map e0.toMonoidHom with hBn
  have hcardBct : Nat.card ↥Bct = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBle).toEquiv
  have hcardBn : Nat.card ↥Bn = Nat.card B := by
    rw [hBn, Subgroup.card_map_of_injective (K := Bct) e0.injective, hcardBct]
  have hoddBn : Odd (Nat.card ↥Bn) := by rw [hcardBn]; exact hBodd
  obtain ⟨hcycBn, _⟩ := Work.L2F.Dihedral.dihedral_oddSubgroup Bn hoddBn
  have hcycBct : IsCyclic ↥Bct :=
    (MulEquiv.isCyclic (Subgroup.equivMapOfInjective Bct e0.toMonoidHom e0.injective)).mpr hcycBn
  have hcycB : IsCyclic ↥B := (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hBle)).mp hcycBct
  have hcycA : IsCyclic A :=
    (MulEquiv.isCyclic (Subgroup.equivMapOfInjective A φ.toMonoidHom φ.injective)).mpr hcycB
  refine ⟨hcycA, ?_⟩
  -- Part 2: action of the normalizer
  intro g hg a ha
  by_cases hAbot : A = ⊥
  · have ha1 : a = 1 := by rw [hAbot] at ha; exact Subgroup.mem_bot.mp ha
    rw [ha1]; simp
  · have hcardA_ne1 : Nat.card A ≠ 1 := fun h1 => hAbot ((Subgroup.card_eq_one).mp h1)
    obtain ⟨r, hrprime, hrdvdA⟩ := Nat.exists_prime_and_dvd hcardA_ne1
    -- a generator of the cyclic group `B`
    obtain ⟨z, hzgen⟩ := IsCyclic.exists_generator (α := ↥B)
    have hBz : B = Subgroup.zpowers (z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) := by
      apply le_antisymm
      · intro b hb
        rw [Subgroup.mem_zpowers_iff]
        have hb' := hzgen ⟨b, hb⟩
        rw [Subgroup.mem_zpowers_iff] at hb'
        obtain ⟨m, hm⟩ := hb'
        refine ⟨m, ?_⟩
        have hmv : ((z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) ^ m) = b := by
          have := congrArg (Subgroup.subtype B) hm
          simpa using this
        exact hmv
      · rw [Subgroup.zpowers_le]; exact z.2
    have hNz : orderOf (z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) = Nat.card A := by
      rw [← Nat.card_zpowers (z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)), ← hBz, hBcard]
    have hrdvdz : r ∣ orderOf (z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) := by
      rw [hNz]; exact hrdvdA
    -- the unique subgroup of order `r` in `B`
    set Br : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
      Subgroup.zpowers ((z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) ^
        (orderOf (z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) / r)) with hBr
    have hBrcard : Nat.card Br = r := by
      rw [hBr]; exact CardZpowersDiv (z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) hrprime hrdvdz
    have hr2 : r ≠ 2 := by
      intro h
      exact hodd.not_two_dvd_nat (h ▸ hrdvdA)
    -- `p ∤ |A|`, so `r ≠ p` and the torus normalizer applies
    have hkne0 : k ≠ 0 := by rintro rfl; simp only [pow_zero] at hk; omega
    have hp_pk : p ∣ p ^ k := dvd_pow_self p hkne0
    have hcardCt : Nat.card ↥Ct = 2 * n := by
      haveI : NeZero n := ⟨by rcases hn with h | h <;> omega⟩
      rw [Nat.card_congr (MulEquiv.toEquiv e0), Nat.card_eq_fintype_card, DihedralGroup.card]
    have hcardA_dvd : Nat.card A ∣ 2 * n := by
      rw [← hBcard, ← hcardBct, ← hcardCt]
      exact Subgroup.card_subgroup_dvd_card Bct
    have hpndvd : ¬ p ∣ Nat.card A := by
      intro hpd
      have hp2n : p ∣ 2 * n := hpd.trans hcardA_dvd
      have hone_le : 1 ≤ p ^ k := by
        have := pow_pos (Fact.out : Nat.Prime p).pos k; omega
      rcases hn with h | h
      · have hd : p ∣ p ^ k - (p ^ k - 1) := by
          rw [h] at hp2n
          exact Nat.dvd_sub hp_pk hp2n
        rw [Nat.sub_sub_self hone_le] at hd
        exact (Fact.out : Nat.Prime p).not_dvd_one hd
      · have hd : p ∣ p ^ k + 1 - p ^ k := Nat.dvd_sub (h ▸ hp2n) hp_pk
        rw [Nat.add_sub_cancel_left] at hd
        exact (Fact.out : Nat.Prime p).not_dvd_one hd
    have hrp : r ≠ p := by
      intro h
      exact hpndvd (h ▸ hrdvdA)
    -- torus structure of the normalizer of the order-`r` subgroup
    obtain ⟨hcycR, hcardR, hnorm⟩ := l2torusNorm p k hp hk r hrprime hr2 hrp Br hBrcard
    set R : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
      Subgroup.centralizer (Br : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) with hR
    set D : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
      Subgroup.normalizer (Br : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) with hD
    obtain ⟨e2⟩ := hnorm
    -- `Br ≤ B ≤ R`
    have hBr_le_B : Br ≤ B := by
      rw [hBr, Subgroup.zpowers_le]
      exact Subgroup.pow_mem B z.2 _
    have hzp_comm : ∀ (u : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))
        (c d : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)),
        c ∈ Subgroup.zpowers u → d ∈ Subgroup.zpowers u → c * d = d * c := by
      intro u c d hc hd
      obtain ⟨kc, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      obtain ⟨kd, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
      rw [← zpow_add, ← zpow_add, add_comm]
    have hB_le_R : B ≤ R := by
      intro b hb
      rw [hR, Subgroup.mem_centralizer_iff]
      intro u hu
      have hb' : b ∈ Subgroup.zpowers (z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) := by
        rw [← hBz]; exact hb
      have hu' : u ∈ Subgroup.zpowers (z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) := by
        rw [← hBz]; exact hBr_le_B hu
      exact hzp_comm _ u b hu' hb'
    have hRD : R ≤ D := by
      rw [hR, hD]
      exact Subgroup.centralizer_le_normalizer (Br : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)))
    have hBr_le_D : Br ≤ D := by rw [hD]; exact Subgroup.le_normalizer
    -- the image of `Br` in the abstract dihedral group
    set X : Subgroup (DihedralGroup (Nat.card ↥R)) := (Br.subgroupOf D).map e2.toMonoidHom with hX
    have hXcard : Nat.card ↥X = r := by
      rw [hX, Subgroup.card_map_of_injective e2.injective]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBr_le_D).toEquiv]
      exact hBrcard
    have hXne : X ≠ ⊥ := by
      intro h
      have h1 : Nat.card ↥X = 1 := by rw [h]; exact Subgroup.card_bot
      rw [hXcard] at h1
      have := hrprime.two_le
      omega
    have hXodd : Odd (Nat.card ↥X) := by rw [hXcard]; exact hrprime.odd_of_ne_two hr2
    -- `φ g ∈ D`
    have hgB : φ g ∈ Subgroup.normalizer (B : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) := by
      have h1 : φ g ∈ (Subgroup.normalizer (A : Set G)).map φ.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
      rwa [Subgroup.map_equiv_normalizer_eq A φ, ← hB] at h1
    have hgD : φ g ∈ D := by
      have h2 : φ g ∈ Subgroup.normalizer (Subgroup.zpowers (z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) := by
        rwa [← hBz]
      have h3 := NormalizerZpowersDiv (z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) hrprime hrdvdz h2
      rw [hD]; exact h3
    -- `φ a ∈ R`
    have hφaB : φ a ∈ B := by rw [hB]; exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have haR : φ a ∈ R := hB_le_R hφaB
    -- the action of `e2 gD` on `e2 aD`
    let gD : ↥D := ⟨φ g, hgD⟩
    let aD : ↥D := ⟨φ a, hRD haR⟩
    have haDval : (aD : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) = φ a := rfl
    have htaD : e2 aD ∈ Subgroup.centralizer (X : Set (DihedralGroup (Nat.card ↥R))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [hX] at hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hyval : (((y : ↥D)) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) ∈ Br :=
        Subgroup.mem_subgroupOf.mp hy
      have hcomm : (((y : ↥D)) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) * (φ a)
          = (φ a) * (((y : ↥D)) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
        (Subgroup.mem_centralizer_iff.mp haR) _ hyval
      change e2.toMonoidHom (y : ↥D) * e2.toMonoidHom aD
        = e2.toMonoidHom aD * e2.toMonoidHom (y : ↥D)
      rw [← map_mul, ← map_mul]
      have hdom : (y : ↥D) * aD = aD * (y : ↥D) := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [haDval]
        exact hcomm
      rw [hdom]
    have hKEY : e2 gD * e2 aD * (e2 gD)⁻¹ = e2 aD ∨
        e2 gD * e2 aD * (e2 gD)⁻¹ = (e2 aD)⁻¹ :=
      DihedralConjCentralizerOdd X hXne hXodd (e2 gD) (e2 aD) htaD
    -- transport back to `G`
    rcases hKEY with h | h
    · left
      apply φ.injective
      have hD' : gD * aD * gD⁻¹ = aD := e2.injective (by simpa only [map_mul, map_inv] using h)
      have hq : φ g * φ a * (φ g)⁻¹ = φ a := by
        have := congrArg (Subtype.val) hD'
        simpa using this
      simpa [map_mul, map_inv] using hq
    · right
      apply φ.injective
      have hD' : gD * aD * gD⁻¹ = aD⁻¹ := e2.injective (by simpa only [map_mul, map_inv] using h)
      have hq : φ g * φ a * (φ g)⁻¹ = (φ a)⁻¹ := by
        have := congrArg (Subtype.val) hD'
        simpa using this
      simpa [map_mul, map_inv] using hq

end Work.CORE4
