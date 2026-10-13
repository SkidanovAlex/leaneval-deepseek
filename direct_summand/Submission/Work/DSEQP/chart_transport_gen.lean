import Mathlib
import Submission.Work.DSEQP.vanishing_ideal_chart

namespace Work.DSEQP

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

theorem chart_transport_gen {S : Type*} [CommRing S] {σ : Type*} [SetLike σ S]
    [AddSubgroupClass σ S] {𝒜 : ℕ → σ} [GradedRing 𝒜] {Y : Scheme}
    (i : Y ⟶ Proj 𝒜) {F G : S} {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (hF : F ∈ 𝒜 d) (hG : G ∈ 𝒜 e) :
    (((i.ker.ideal ⟨Proj.basicOpen 𝒜 F, Proj.isAffineOpen_basicOpen 𝒜 F hF hd⟩)).comap
        (CommRingCat.Hom.hom (Proj.basicOpenIsoAway 𝒜 F hF hd).hom)).map
      (awayMap 𝒜 hG (show F*G = F*G from rfl)) =
    (((i.ker.ideal ⟨Proj.basicOpen 𝒜 G, Proj.isAffineOpen_basicOpen 𝒜 G hG he⟩)).comap
        (CommRingCat.Hom.hom (Proj.basicOpenIsoAway 𝒜 G hG he).hom)).map
      (awayMap 𝒜 hF (show F*G = G*F from mul_comm F G)) := by
  have hFG : F*G ∈ 𝒜 (d+e) := SetLike.mul_mem_graded hF hG
  have hde : 0 < d + e := Nat.add_pos_left hd e
  let W : (Proj 𝒜).affineOpens :=
    ⟨Proj.basicOpen 𝒜 (F*G), Proj.isAffineOpen_basicOpen 𝒜 (F*G) hFG hde⟩
  let Vf : (Proj 𝒜).affineOpens :=
    ⟨Proj.basicOpen 𝒜 F, Proj.isAffineOpen_basicOpen 𝒜 F hF hd⟩
  let Vg : (Proj 𝒜).affineOpens :=
    ⟨Proj.basicOpen 𝒜 G, Proj.isAffineOpen_basicOpen 𝒜 G hG he⟩
  let φf : (Away 𝒜 F) →+* Γ(Proj 𝒜, Proj.basicOpen 𝒜 F) :=
    CommRingCat.Hom.hom (Proj.basicOpenIsoAway 𝒜 F hF hd).hom
  let φg : (Away 𝒜 G) →+* Γ(Proj 𝒜, Proj.basicOpen 𝒜 G) :=
    CommRingCat.Hom.hom (Proj.basicOpenIsoAway 𝒜 G hG he).hom
  let ψ : (Away 𝒜 (F*G)) →+* Γ(Proj 𝒜, Proj.basicOpen 𝒜 (F*G)) :=
    CommRingCat.Hom.hom (Proj.basicOpenIsoAway 𝒜 (F*G) hFG hde).hom
  have hsurjψ : Function.Surjective ψ :=
    (ConcreteCategory.bijective_of_isIso (Proj.basicOpenIsoAway 𝒜 (F*G) hFG hde).hom).2
  have hinjψ : Function.Injective ψ :=
    (ConcreteCategory.bijective_of_isIso (Proj.basicOpenIsoAway 𝒜 (F*G) hFG hde).hom).1
  have hsurjφg : Function.Surjective φg :=
    (ConcreteCategory.bijective_of_isIso (Proj.basicOpenIsoAway 𝒜 G hG he).hom).2
  have hsurjφf : Function.Surjective φf :=
    (ConcreteCategory.bijective_of_isIso (Proj.basicOpenIsoAway 𝒜 F hF hd).hom).2
  have hkerψ : Ideal.comap ψ ⊥ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Ideal.mem_comap, Ideal.mem_bot] at hy
    exact hinjψ (by rw [hy, map_zero])
  have hWf : W ≤ Vf := by
    show Proj.basicOpen 𝒜 (F*G) ≤ Proj.basicOpen 𝒜 F
    rw [Proj.basicOpen_mul]; exact inf_le_left
  have hWg : W ≤ Vg := by
    show Proj.basicOpen 𝒜 (F*G) ≤ Proj.basicOpen 𝒜 G
    rw [Proj.basicOpen_mul]; exact inf_le_right
  change ((i.ker.ideal Vf).comap φf).map (awayMap 𝒜 hG (show F*G = F*G from rfl)) =
    ((i.ker.ideal Vg).comap φg).map (awayMap 𝒜 hF (show F*G = G*F from mul_comm F G))
  let ρf : Γ(Proj 𝒜, Proj.basicOpen 𝒜 F) →+* Γ(Proj 𝒜, Proj.basicOpen 𝒜 (F*G)) :=
    CommRingCat.Hom.hom ((Proj 𝒜).presheaf.map (homOfLE hWf).op)
  let ρg : Γ(Proj 𝒜, Proj.basicOpen 𝒜 G) →+* Γ(Proj 𝒜, Proj.basicOpen 𝒜 (F*G)) :=
    CommRingCat.Hom.hom ((Proj 𝒜).presheaf.map (homOfLE hWg).op)
  have hhomf : (homOfLE (Proj.basicOpen_mono 𝒜 F (F*G) ⟨G, rfl⟩) :
      Proj.basicOpen 𝒜 (F*G) ⟶ Proj.basicOpen 𝒜 F) = homOfLE hWf := rfl
  have hhomg : (homOfLE (Proj.basicOpen_mono 𝒜 G (F*G) ⟨F, mul_comm F G⟩) :
      Proj.basicOpen 𝒜 (F*G) ⟶ Proj.basicOpen 𝒜 G) = homOfLE hWg := rfl
  have hsqf : ψ.comp (awayMap 𝒜 hG (show F*G = F*G from rfl)) = ρf.comp φf := by
    have h := Proj.awayMap_awayToSection (𝒜 := 𝒜) (f := F) (g := G) hG (x := F*G) rfl
    rw [← Proj.basicOpenIsoAway_hom (𝒜 := 𝒜) (f := F*G) hFG hde,
        ← Proj.basicOpenIsoAway_hom (𝒜 := 𝒜) (f := F) hF hd] at h
    have h2 := congrArg CommRingCat.Hom.hom h
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h2
    rw [hhomf] at h2
    exact h2
  have hsqg : ψ.comp (awayMap 𝒜 hF (show F*G = G*F from mul_comm F G)) = ρg.comp φg := by
    have h := Proj.awayMap_awayToSection (𝒜 := 𝒜) (f := G) (g := F) hF (x := F*G)
      (mul_comm F G)
    rw [← Proj.basicOpenIsoAway_hom (𝒜 := 𝒜) (f := F*G) hFG hde,
        ← Proj.basicOpenIsoAway_hom (𝒜 := 𝒜) (f := G) hG he] at h
    have h2 := congrArg CommRingCat.Hom.hom h
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h2
    rw [hhomg] at h2
    exact h2
  have keyf : ((i.ker.ideal Vf).comap φf).map (awayMap 𝒜 hG (show F*G = F*G from rfl)) =
      (i.ker.ideal W).comap ψ := by
    have h1 : Ideal.map ψ (Ideal.map (awayMap 𝒜 hG (show F*G = F*G from rfl))
        (Ideal.comap φf (i.ker.ideal Vf))) = i.ker.ideal W := by
      rw [Ideal.map_map, hsqf, ← Ideal.map_map, Ideal.map_comap_of_surjective _ hsurjφf]
      exact Scheme.IdealSheafData.map_ideal i.ker hWf
    rw [← h1, Ideal.comap_map_of_surjective ψ hsurjψ, hkerψ, sup_bot_eq]
  have keyg : ((i.ker.ideal Vg).comap φg).map (awayMap 𝒜 hF (show F*G = G*F from mul_comm F G)) =
      (i.ker.ideal W).comap ψ := by
    have h1 : Ideal.map ψ (Ideal.map (awayMap 𝒜 hF (show F*G = G*F from mul_comm F G))
        (Ideal.comap φg (i.ker.ideal Vg))) = i.ker.ideal W := by
      rw [Ideal.map_map, hsqg, ← Ideal.map_map, Ideal.map_comap_of_surjective _ hsurjφg]
      exact Scheme.IdealSheafData.map_ideal i.ker hWg
    rw [← h1, Ideal.comap_map_of_surjective ψ hsurjψ, hkerψ, sup_bot_eq]
  rw [keyf, keyg]

end Work.DSEQP
